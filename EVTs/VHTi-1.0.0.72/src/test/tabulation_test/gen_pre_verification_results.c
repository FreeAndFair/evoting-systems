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
#include "vhti/gen_pre_verification_results.h"
#include <stdio.h>
#include <malloc.h>

static void
expect_gen_pre_vv_results (CuTest *tc,
                           int expected_status,
                           VoteVerificationKey const vv_key,
                           SignedVotedBallots const signed_voted_ballots,
                           SignedBlankBallot const signed_blank_ballot,
                           GeneralPurposePublicKey ballot_signing_key)
{
   char *pre_vcode_box = 0;

   CuAssert (tc,
             (0 == expected_status
              ? "VHTI_generate_pre_verification_results of valid inputs should have succeeded"
              : "VHTI_generate_pre_verification_results of invalid inputs should have failed"),
             expected_status == VHTI_generate_pre_verification_results
             ( vv_key,
               signed_voted_ballots, signed_blank_ballot, ballot_signing_key , &pre_vcode_box));

   if (0 != expected_status)
   {
      if (pre_vcode_box) {
         fprintf (stderr, "Hmm: `%s'\n", pre_vcode_box);
      }
      CuAssertPtrEquals (tc, NULL, pre_vcode_box);
   }
   else
   {
      CuAssertPtrNotNull (tc, pre_vcode_box);
      CuAssert (tc, "VHTI_generate_pre_verification_results should have returned a PreVerificationCodeBox.",
                0 == (VHTI_validate (PRE_VERIFICATION_CODE_BOX, pre_vcode_box)));
      
      VHTI_free (pre_vcode_box);
      pre_vcode_box = 0;
   }
}

void
gen_pre_vv_results_validation (CuTest *tc)
{
   expect_gen_pre_vv_results (tc,  0,   valid_vkey,   valid_svbs,   valid_sbb, valid_pubkey);
   expect_gen_pre_vv_results (tc, -1, invalid_vkey,   valid_svbs,   valid_sbb, valid_pubkey);
   expect_gen_pre_vv_results (tc, -1,   valid_vkey, invalid_svbs,   valid_sbb, valid_pubkey);
   expect_gen_pre_vv_results (tc, -1,   valid_vkey,   valid_svbs, invalid_sbb, valid_pubkey);
}
