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
#include "vhti/gen_pv_results.h"
#include "misc/xml_tree.h"
#include "util/sslerror.h"
#include <support/internal_error.h>
#include <tabulation/tabulation_internal.h>
#include <support/support_internal.h>
#include <support/random_internal.h>
#include <support/bignum.h>
#include <support/xml_tree_group_check.h>
#include <string.h>
#include <sstream>

int
VHTI_generate_partial_verification_results
(PreVerificationCodeBoxes pre_vcode_boxes,
 SignedBlankBallot signed_blank_ballot,
 GeneralPurposePublicKey ballot_signing_key,
 CommittedAuthority committed_authority,
 SecretShare secret_share,
 RandomState random_state,
 AuthorityPartialDecrypt *auth_partial_decrypt_of_verifications,
 RandomState *random_state_out)
{
   // Assume success until told otherwise
   int result = 0;
   // A counter used for loops
   int icount=0;
   *auth_partial_decrypt_of_verifications = NULL;
   *random_state_out = NULL;
   auto_BN pm(NULL); // The Election Modulus
   auto_BN qm(NULL); // The Election Subgroup Modulus
   auto_BN gen(NULL); // The Election Subgroup Generator
   auto_BN ePublicKey(NULL); // The Election Public Key
   // An OpenSSL structure that holds BIGNUM temporary variables
   // used by library functions
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx)
      throw SSL_ERROR;

   try
   {
      result = (::VHTI_validate(PRE_VERIFICATION_CODE_BOXES, pre_vcode_boxes)
         || ::VHTI_validate(SIGNED_BLANK_BALLOT, signed_blank_ballot)
         || ::VHTI_validate(COMMITTED_AUTHORITY, committed_authority)
         || ::VHTI_validate(SECRET_SHARE, secret_share)
         || ::VHTI_validate(RANDOM_STATE, random_state));

      if (result != 0) throw VH_exception("VALIDATION_FAILURE");

      // An xml tree from the signed_blank_ballot input
      VHUtil::xml_tree_group_check xml_bb(signed_blank_ballot,
                                           BLANK_BALLOT,
                                           ballot_signing_key,
                                           pm, qm, gen, ePublicKey);
      // Check the pre_vcode_boxes input
      VHUtil::xml_tree_group_check xml_pvb(pre_vcode_boxes, pm, qm, gen, ePublicKey);
      // Check the committed_authority input
      VHUtil::xml_tree_group_check xml_ca(committed_authority, pm, qm, gen, ePublicKey);
      // Check the secret_share input
      VHUtil::xml_tree_group_check xml_ss(secret_share, pm, qm, gen, ePublicKey);
      
      // Send the PreVerificationCodeBoxes to get multiplied together
      // The returning RawBallotBox from combine_pre_vv_results
      auto_freeing < RawBallotBox > verification_raw_ballot_box = 0;
      VHInternal::combine_pre_vv_results
         (pre_vcode_boxes,
          xml_bb,
          &verification_raw_ballot_box);

      // Send this RawBallotBox to partial_decrypt
      // The returning AuthorityPartialDecrypt from VHTI_partial_decrypt
      auto_freeing<AuthorityPartialDecrypt> auth_partial_decrypt = 0;
      // The returning RandomState from VHTI_partial_decrypt
      auto_freeing<RandomState> return_random_state = 0;
      result = VHTI_partial_decrypt
         (verification_raw_ballot_box,
          signed_blank_ballot, ballot_signing_key,
          committed_authority, secret_share,
          random_state, &auth_partial_decrypt, &return_random_state);
      if (!result)
      {
         *auth_partial_decrypt_of_verifications =
            VHTI_dup(auth_partial_decrypt);
         *random_state_out = VHTI_dup(return_random_state);
      }
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      result = e.getResultNo();
   }
   
   return result;
   
}
