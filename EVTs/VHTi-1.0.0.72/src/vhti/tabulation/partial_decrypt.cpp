/*  */
/* This material is subject to the VoteHere Source Code Evaluation */
/* License Agreement ("Agreement").  Possession and/or use of this */
/* material indicates your acceptance of this Agreement in its entirety. */
/* Copies of the Agreement may be found at www.votehere.net. */
/*  */
/* Copyright 2004 VoteHere, Inc.  All Rights Reserved */
/*  */
/* You may not download this Software if you are located in any country */
/* (or are a national of a country) subject to a general U.S. or */
/* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, */
/* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States */
/* (each a "Prohibited Country") or are otherwise denied export */
/* privileges from the United States or Canada ("Denied Person"). */
/* Further, you may not transfer or re-export the Software to any such */
/* country or Denied Person without a license or authorization from the */
/* U.S. government.  By downloading the Software, you represent and */
/* warrant that you are not a Denied Person, are not located in or a */
/* national of a Prohibited Country, and will not export or re-export to */
/* any Prohibited Country or Denied Party. */
// Copyright 2003 VoteHere Inc. All Rights Reserved.

#include "vhti/partial_decrypt.h"
#include "util/sslerror.h"
#include "misc/xml_tree.h"
#include "misc/array.h"
#include <support/internal_error.h>
#include <tabulation/tabulation_internal.h>
#include <support/support_internal.h>
#include <support/random_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <string.h>
#include <sstream>

int
VHTI_partial_decrypt (RawBallotBox raw_ballot_box,
                      SignedBlankBallot signed_blank_ballot,
                      GeneralPurposePublicKey ballot_signing_key,
                      CommittedAuthority committed_authority,
                      SecretShare secret_share,
                      RandomState random_state,
                      AuthorityPartialDecrypt *auth_partial_decrypt,
                      RandomState *random_state_out)
{
   int result = 0; // Assume success until told otherwise
   *auth_partial_decrypt = NULL;
   *random_state_out = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx) throw SSL_ERROR;

   try {
      result = (::VHTI_validate(RAW_BALLOT_BOX, raw_ballot_box)
         || ::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot)
         || ::VHTI_validate(COMMITTED_AUTHORITY, committed_authority)
         || ::VHTI_validate(SECRET_SHARE, secret_share)
         || ::VHTI_validate(RANDOM_STATE, random_state));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      VHInternal::RS rs (random_state); // A RandomState object

      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_sbb(signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);
      // xml tree from secret_share input
      VHUtil::xml_tree_group_check xml_ss(secret_share, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_ss = xml_ss.root(); // The root node of xml_ss
      auto_BN secret = xml2BN(root_ss); // The value of the SecretShare
      // An xml tree from the committed_authority input
      VHUtil::xml_tree_group_check xml_comm_auth(committed_authority,
         pm, qm, gen, ePublicKey);
      // The root node of xml_comm_auth
      VHUtil::xml_node root_comm_auth = xml_comm_auth.root();
      
      // Construct empty AuthorityPartialDecrypt and insert authority
      VHUtil::xml_tree xml_auth_pd("<" AUTHORITY_PARTIAL_DECRYPT "/>");
      // The root node of xml_auth_pd
      VHUtil::xml_node root_auth_pd = xml_auth_pd.root();
      root_auth_pd->add_element(root_comm_auth->deep_copy());
      // A node to hold the BallotBoxPartialDecrypt
      VHUtil::xml_node root_bbpd =
         root_auth_pd->new_element(BALLOT_BOX_PARTIAL_DECRYPT);
      // An xml tree from the raw_ballot_box input
      VHUtil::xml_tree_group_check xml_rbb(raw_ballot_box, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_rbb = xml_rbb.root(); // The root node of xml_rbb
      
      // Calculate partially decrypted XValue for each ElGamal pair
      int num_rbb_elems = root_rbb->element_count();  // RawVotedBallot count
      for (int i=0; i<num_rbb_elems; i++)
      {  // A node to hold the BallotPartialDecrypt
         VHUtil::xml_node root_bpd =
            root_bbpd->new_element(BALLOT_PARTIAL_DECRYPT);
         
         VHUtil::xml_node rvb_node = root_rbb->e(i); // Current RawVotedBallot
         int num_rvb_elems = rvb_node->element_count();  //ElGamal pair count
         for (int j=0; j<num_rvb_elems; j++)
         {  // The X node of the current ElGamalPair
            VHUtil::xml_node x_node = rvb_node->e(j)->e(X_VALUE);
            auto_BN xval = xml2BN(x_node); // The value of the XValue
            
            // A node to hold the AnswerPartialDecrypt
            VHUtil::xml_node root_answer =
               root_bpd->new_element(ANSWER_PARTIAL_DECRYPT);
            auto_BN new_xval; // new_xval = XValue^secret
            if (!BN_mod_exp(new_xval, xval, secret, pm, ctx)) throw SSL_ERROR;
            
            // Add it to your AnswerPartialDecrypt object
            add_BN_element(root_answer, X_VALUE, new_xval);
            // For each new_xval, which is the partially decrypted value,
            // we need to generate a proof.  The proof looks much like the
            // zero-knowledge proof done for checking broadcast values.
            
            auto_BN omega(NULL); // An auto_BN for a random omega
            auto_BN one_bn; // A BIGNUM with the value of 1
            if (!BN_one(one_bn)) throw SSL_ERROR;
            VHInternal::rand_range2(one_bn, qm, rs, omega);
            
            auto_BN proof_var_A;  // "A" is X^omega
            if (!BN_mod_exp(proof_var_A, xval, omega, pm, ctx)) throw SSL_ERROR;
            auto_BN proof_var_B;  // "B" is g^omega
            VHInternal::fixed_mod_exp(proof_var_B, gen, omega,
                                      pm, ctx);
            
            auto_BN key_share_commitment;  // KSC is g^secret
            VHInternal::fixed_mod_exp(key_share_commitment, gen,
                                      secret, pm, ctx);
            
            // hash (x, X, y, Y, A, B) ==> (xval, new_xval, gen, KSC, A, B)
            // An array to hold the values to hash
            const BIGNUM * arr[] = {xval, new_xval, gen, key_share_commitment,
               proof_var_A, proof_var_B};
            
            auto_BN c_const; // The hash value in Zq
            // The hash value before taking the modulus
            auto_BN tmp_hash = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
            if (!BN_mod(c_const, tmp_hash, qm, ctx)) throw SSL_ERROR;
            
            auto_BN d_func;  // The function "d"
            auto_BN tmp_prod; // The product of c_const and the secret
            if (!BN_mod_mul(tmp_prod, c_const, secret, qm, ctx)
                || !BN_sub(d_func, omega, tmp_prod)) throw SSL_ERROR;
            d_func.Canonicalize(qm);
            // add "C" and "d" to your AnswerPartialDecrypt object
            add_BN_element(root_answer, CONSTANT_VAL, c_const);
            add_BN_element(root_answer, FUNCTION_VAL, d_func);
         }
      }
      std::ostringstream auth_pd_stream; // A stream to hold xml_auth_pd
      auth_pd_stream << xml_auth_pd;
      *auth_partial_decrypt = VHTI_dup(auth_pd_stream.str().c_str());
      *random_state_out = VHTI_dup (rs);
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
