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

#include "tabulation_test.h"
#include <misc/cutest.h>
#include "support_test/test-data.h"
#include "vhti/types.h"
#include "vhti/gen_pv_results.h"
#include <stdio.h>
#include <malloc.h>

static void
expect_gen_partial_vv_results (CuTest *tc,
                               int expected_status,
                               PreVerificationCodeBoxes const pre_vcode_boxes,
                               SignedBlankBallot const signed_blank_ballot,
                               GeneralPurposePublicKey ballot_signing_key,
                               CommittedAuthority const committed_authority,
                               SecretShare const secret_share,
                               RandomState const random_state)
{
   char *auth_partial_decrypt_of_verifications = 0;
   char *random_state_out = 0;

   CuAssert (tc,
             (0 == expected_status
              ? "VHTI_generate_partial_verification_results of valid inputs should have succeeded"
              : "VHTI_generate_partial_verification_results of invalid inputs should have failed"),
             expected_status == VHTI_generate_partial_verification_results
             ( pre_vcode_boxes,
               signed_blank_ballot, ballot_signing_key,
               committed_authority, secret_share, random_state,
               &auth_partial_decrypt_of_verifications, &random_state_out));

   if (0 != expected_status)
   {
      if (auth_partial_decrypt_of_verifications) {
         fprintf (stderr, "Hmm: `%s'\n", auth_partial_decrypt_of_verifications);
      }
      CuAssertPtrEquals (tc, NULL, auth_partial_decrypt_of_verifications);

      if (random_state_out) {
         fprintf (stderr, "Hmm: `%s'\n", random_state_out);
      }
      CuAssertPtrEquals (tc, NULL, random_state_out);
   }
   else
   {
      CuAssertPtrNotNull (tc, auth_partial_decrypt_of_verifications);
      CuAssertPtrNotNull (tc, random_state_out);
      CuAssert (tc, "VHTI_generate_partial_verification_results should have returned an AuthorityPartialDecrypt and a RandomState.",
                0 == (VHTI_validate (AUTHORITY_PARTIAL_DECRYPT, auth_partial_decrypt_of_verifications)
                || VHTI_validate (RANDOM_STATE, random_state_out)));
      
      
      VHTI_free (auth_partial_decrypt_of_verifications);
      auth_partial_decrypt_of_verifications = 0;
      VHTI_free (random_state_out);
      random_state_out = 0;
   }
}

void
gen_partial_vv_results_validation (CuTest *tc)
{
   expect_gen_partial_vv_results (tc,  0,   valid_pvc_boxes,   valid_sbb, valid_pubkey,   valid_committed_authority,   valid_secret_share,   valid_random_state);
   expect_gen_partial_vv_results (tc, -1, invalid_pvc_boxes,   valid_sbb, valid_pubkey,   valid_committed_authority,   valid_secret_share,   valid_random_state);
   expect_gen_partial_vv_results (tc, -1,   valid_pvc_boxes, invalid_sbb, valid_pubkey,   valid_committed_authority,   valid_secret_share,   valid_random_state);
   expect_gen_partial_vv_results (tc, -1,   valid_pvc_boxes,   valid_sbb, valid_pubkey, invalid_committed_authority,   valid_secret_share,   valid_random_state);
   expect_gen_partial_vv_results (tc, -1,   valid_pvc_boxes,   valid_sbb, valid_pubkey,   valid_committed_authority, invalid_secret_share,   valid_random_state);
   expect_gen_partial_vv_results (tc, -1,   valid_pvc_boxes,   valid_sbb, valid_pubkey,   valid_committed_authority,   valid_secret_share, invalid_random_state);
}
