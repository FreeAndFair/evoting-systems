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

#include "vhti/check_comm.h"
#include "vhti/keyshare_util.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <keyshare/keyshare_internal.h>
#include <misc/xml_tree.h>

#include <string>
#include <sstream>
#include <cassert>

// Any of the authorities may call this function
// to check the commitment of any other authority
// (or to check their own).  The authority_id is
// the owner of the commitment being checked.

int
VHTI_check_commitment (KeyGenParameters key_gen_parameters,
                       // Authority whose commitment we want to check
                       Authority authority,
                       BroadcastValues broadcast_values,
                       KeyShareCommitment keyshare_commitment,
                       CheckResults *check_comm_results)
{
   int result = 0; // This will be nonzero if we were somehow unable
                   // to check.  But even if it's zero, the commitment
                   // might still be bad.  Assume success until told
                   // otherwise.
   bool fCheckSuccess = true;   // this is relevant only if result is zero.
   *check_comm_results = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key - not used here
   int na = 0; // The number of authorities
   int th = 0; // The threshold number of authorities needed for tabulation
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   std::string auth_id; // Also known as the AuthorityFingerprint
   // A vector to hold the theta values for the current authority
   std::vector< auto_BN > tht_beta;
   
   try
   {
      VH_nonzero (ctx, BN_CTX_NEW);
      result = (::VHTI_validate(KEY_GEN_PARAMETERS, key_gen_parameters)
         || ::VHTI_validate(AUTHORITY, authority)
         || ::VHTI_validate(BROADCAST_VALUES, broadcast_values)
         || ::VHTI_validate(KEY_SHARE_COMMITMENT, keyshare_commitment));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");
      VHUtil::xml_tree xml_res("<" CHECK_RESULTS "/>");  // Empty results object

      VHInternal::get_keygen_parameters (key_gen_parameters, pm, qm, gen,
         na, th);
      
      // Get Beta for AuthCertFingerprint=ToID from authority_id.
       // xml tree from the authority input
      VHUtil::xml_tree_group_check xml_auth(authority, pm, qm, gen, ePublicKey);

      auth_id = xml_auth.root ()->attribute(AUTH_FINGERPRINT);
      // The unique BIGNUM associated with this authority
      auto_BN beta = xml2BN(xml_auth.root ()->e(AUTHORITY_EVALUATION_POINT));
      
      // An xml tree from the authority's keyshare_commitment
      VHUtil::xml_tree_group_check xml_ksc(keyshare_commitment, pm, qm, gen, ePublicKey);

      auto_BN bn_ksc = xml2BN(xml_ksc.root ()); // The value of the KeyShareCommitment
      
      if (xml_ksc.root ()->attribute(AUTH_FINGERPRINT) != auth_id)
         // mismatch between authority_id and keyshare_commitment
         fCheckSuccess = false;
      else
      {
         // Since we know that sbeta = f(beta), we can raise g to
         // both sides, and note that g^sbeta == Commitment.
         // So we need to check that the Commitment for each authority
         // equals the other side, which works out to be
         // multiply from all auths( Theta0, Theta1^beta, Theta2^(beta^2),
         // ... , Thetat^(beta^(t-1)))
         // An xml tree from the broadcast_values input
         VHUtil::xml_tree_group_check xml_bvs(broadcast_values, pm, qm, gen, ePublicKey);

         for (int bvs = 0;
              bvs<xml_bvs.root ()->element_count();
              bvs++)
         {  
            // We are going to collect terms from ALL of the authorities

            VHUtil::xml_node current_node = NULL;
            for (int i = 0;
                 current_node = xml_bvs.root ()->e(bvs)->element(BIG_THETA, i);
                 i++)
            {
               auto_BN tht = xml2BN(current_node); // The current value of Theta

               BIGNUM * orderBN = BN_new(); // Turn it into a BIGNUM
               VH_nonzero (orderBN, BN_NEW);
               VH_nonzero (BN_dec2bn(&orderBN, current_node->attribute(ORDER).c_str()), BN_DEC2BN);
               
               auto_BN tmp_exp1;  // raise beta to the Order
               VH_nonzero (BN_mod_exp(tmp_exp1, beta, orderBN, qm, ctx),
                           BN_MOD_EXP);
               auto_BN tmp_exp2;  // then raise coefficient to this exp
               VH_nonzero (BN_mod_exp(tmp_exp2, tht, tmp_exp1, pm, ctx),
                           BN_MOD_EXP);
               tht_beta.push_back(tmp_exp2);  // put quotients in a vector
            }
         }
         // Check that you have Threshold*n number of Thetas
         if (tht_beta.size() != th*na)
            fCheckSuccess = false;
         else
         {  // multiply ALL the terms from all the authorities
            // The value we will check against the KeyShareCommitment
            auto_BN comm_chk_val;
            BN_one(comm_chk_val);
            for (int iv=0; iv<tht_beta.size(); iv++) {
               VH_nonzero (BN_mod_mul(comm_chk_val, comm_chk_val, tht_beta[iv], pm, ctx),
                           BN_MOD_MUL);
            }
            fCheckSuccess = (0 == BN_cmp(comm_chk_val, bn_ksc));
         }
      }

      assert (0 == result);

      xml_res.root ()->add_characters(fCheckSuccess
                                      ? CHECK_SUCCESS_TEXT
                                      : CHECK_FAILURE_TEXT);

      std::ostringstream res_stream; // A stream to hold the results
      res_stream << xml_res;
      *check_comm_results = VHTI_dup(res_stream.str().c_str());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   return result;
}
