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

#include "vhti/check_partial_decrypt.h"
#include <misc/xml_tree.h>
#include <util/sslerror.h>
#include <support/bignum.h>
#include <tabulation/tabulation_internal.h>
#include <support/support_internal.h>
#include <support/internal_error.h>
#include <support/xml_tree_group_check.h>
#include <string.h>
#include <sstream>

int
VHTI_check_partial_decrypt (RawBallotBox raw_ballot_box,
                            AuthorityPartialDecrypt auth_partial_decrypt,
                            SignedBlankBallot signed_blank_ballot,
                            GeneralPurposePublicKey ballot_signing_key,
                            CheckResults *check_partial_decrypt_result)
{
   int result = 0; // Assume success until told otherwise
   bool checked = true; // Describes whether partial decrypt has been checked
   *check_partial_decrypt_result = NULL;
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
         || ::VHTI_validate(AUTHORITY_PARTIAL_DECRYPT, auth_partial_decrypt)
         || ::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot));
      
      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_sbb(signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);

      // An xml tree from the raw_ballot_box input
      VHUtil::xml_tree_group_check xml_rbb(raw_ballot_box, pm, qm, gen, ePublicKey);
      VHUtil::xml_node root_rbb = xml_rbb.root(); // The root node of xml_rbb
      
      // An xml tree from the auth_partial_decrypt input
      VHUtil::xml_tree_group_check xml_auth_pd(auth_partial_decrypt, pm, qm, gen, ePublicKey);
      // The root node of xml_auth_pd
      VHUtil::xml_node root_auth_pd = xml_auth_pd.root();
      // The node that contains the BallotBoxPartialDecrypt
      VHUtil::xml_node node_bbpd =root_auth_pd->e(BALLOT_BOX_PARTIAL_DECRYPT);
      
      // Get Authority and KeyShareCommitment out of AuthorityPartialDecrypt
      // The node that contains the KeyShareCommitment
      VHUtil::xml_node node_ksc =
         root_auth_pd->e(COMMITTED_AUTHORITY)->e(KEY_SHARE_COMMITMENT);
      // The value of the KeyShareCommitment
      auto_BN key_share_commitment = xml2BN(node_ksc);
      
      // For each ballot answer on each ballot in ballot box, get:
      // x out of raw_ballot_box, X out of pd_ballot_box
      // "C" and "d" out of DecryptionValidityProof
      // y and Y are the EGenerator and the Authority's KSC, respectively
      
      // Go through the original RBB and the ballot box partial decrypt
      // The number of raw voted ballots in the box
      int rvb_count = root_rbb->element_count();
      // The number of BallotPartialDecrypt objects in the box
      int bpd_count = node_bbpd->element_count();
      if (rvb_count != bpd_count) {
         VHUtil::cout () << "rvb_count " << rvb_count
                         << " != bpd_count " << bpd_count
                         << std::endl;
         checked = false;
         // Different number of ballots in the original raw ballot box
         // and the partially decrypted ballot box
      }
      else {
         for (int i=0; checked && i<rvb_count; i++)
         {  // The current raw voted ballot
            VHUtil::xml_node current_rvb = root_rbb->e(i);
            // The current ballot partial decrypt
            VHUtil::xml_node current_bpd  = node_bbpd->e(i);
            // The number of El Gamal pairs in ballot
            int egp_count = current_rvb->element_count();
            // The number of answers in the ballot partial decrypt
            int bpd_answer_count = current_bpd->element_count();
            
            if (egp_count != bpd_answer_count) {
               VHUtil::cout () << "egp_count " << egp_count
                               << " != bpd_answer_count " << bpd_answer_count
                               << std::endl;
               checked = false;
               break;
               // Different number of El Gamal Pairs in the "same" ballot
               // in the original RVB and the partially decrypted ballot
            }
            
            for (int j=0; checked && j<egp_count; j++)
            {  // The node of the current answer in the partial decrypt
               VHUtil::xml_node current_ans_pd = current_bpd->e(j);
               // The node of the current ElGamal Pair
               VHUtil::xml_node current_egp = current_rvb->e(j);
               
               // The value of c, a member of Zq
               auto_BN c_value = xml2BN(current_ans_pd->e(CONSTANT_VAL));
               // The value of d, a function of c
               auto_BN d_value = xml2BN(current_ans_pd->e(FUNCTION_VAL));
               // The original x value
               auto_BN orig_xval = xml2BN(current_egp->e(X_VALUE));
               // The current x value
               auto_BN pd_xval = xml2BN(current_ans_pd->e(X_VALUE));
               
               auto_BN a_value;  // An auto_BN to hold (X^c)*(x^d)
               auto_BN b_value;  // An auto_BN to hold (Y^c)*(y^d)
               auto_BN tmp_exp_a1;  // The value of X^c
               auto_BN tmp_exp_a2;  // The value of x^d
               auto_BN tmp_exp_b1;  // The value of Y^c
               auto_BN tmp_exp_b2;  // The value of y^d
               
               if (!BN_mod_exp(tmp_exp_a1, pd_xval, c_value, pm, ctx)
                   || !BN_mod_exp(tmp_exp_a2, orig_xval, d_value, pm, ctx)
                   || !BN_mod_mul(a_value, tmp_exp_a1, tmp_exp_a2, pm, ctx)
                   || !BN_mod_exp(tmp_exp_b1, key_share_commitment, c_value,
                                  pm,ctx)
                   || !BN_mod_exp(tmp_exp_b2, gen, d_value, pm, ctx)
                   || !BN_mod_mul(b_value, tmp_exp_b1, tmp_exp_b2, pm, ctx)
                  )
                  throw SSL_ERROR;

               // hash (x, X, y, Y, A, B) ==> (xval, new_xval, gen, KSC, A, B)
               // An array to hold elements to hash
               const BIGNUM * a_ray[] = {orig_xval, pd_xval, gen,
                                        key_share_commitment, a_value, b_value};
               
               // An auto_BN to hold the hash value
               auto_BN hashval;
               // An auto_BN to hold the hash value before taking the modulus
               auto_BN tmp_hash =
                  GetHashOfNBNs(a_ray, sizeof(a_ray) / sizeof(a_ray[0]));
               if (!BN_mod(hashval, tmp_hash, qm, ctx)) throw SSL_ERROR;
               
               if (BN_cmp(c_value, hashval)) {  // Check to see if C = Hash
                  VHUtil::cout () << "c_value " << c_value
                                  << " != hashval " << hashval
                                  << std::endl;
                  checked = false;
                  break;
               }
            }
         }
      }
      // An empty xml tree to hold the CheckResults
      VHUtil::xml_tree xml_res("<" CHECK_RESULTS "/>");
      VHUtil::xml_node root_res = xml_res.root(); // The root node of xml_res
      root_res->add_characters(checked ? CHECK_SUCCESS_TEXT : CHECK_FAILURE_TEXT);
      std::ostringstream res_stream; // A stream to hold xml_res
      res_stream << xml_res;
      *check_partial_decrypt_result = VHTI_dup(res_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e) {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
