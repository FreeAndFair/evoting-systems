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
#include "vhti/check_shuffle.h"
#include <stdio.h>
#include "support_test/test-data.h"
#include "vhti/types.h"
#include <malloc.h>

static void
expect_check_shuffle (CuTest *tc,
                      const int expect_success,
                      RawBallotBox const raw_ballot_box_before,
                      RawBallotBox const raw_ballot_box_after,
                      SignedBlankBallot const signed_blank_ballot,
                      GeneralPurposePublicKey ballot_signing_key,
                      ShuffleValidityProof const shuffle_validity_proof)
{
   char * check_shuffle_result = 0;

   CuAssert (tc,
             (expect_success
              ? "VHTI_check_shuffle of valid inputs should have succeeded"
              : "VHTI_check_shuffle of invalid inputs should have failed"),
             ((1 == expect_success)
              ==
              (0 == VHTI_check_shuffle
               (raw_ballot_box_before, raw_ballot_box_after,
                signed_blank_ballot,
                ballot_signing_key,
                shuffle_validity_proof, &check_shuffle_result))));

   if (!expect_success)
   {
      if (check_shuffle_result)
         fprintf (stderr, "Hmm: `%s'\n", check_shuffle_result);
      CuAssertPtrEquals (tc, NULL, check_shuffle_result);
   }
   else
   {
      CuAssertPtrNotNull (tc, check_shuffle_result);
      CuAssert (tc,
                "VHTI_check_shuffle should have returned CheckResults",
                0 == VHTI_validate (CHECK_RESULTS, check_shuffle_result));
      VHTI_free (check_shuffle_result);
   }
}


void
check_shuffle_validation (CuTest *tc)
{
   expect_check_shuffle (tc, 1, valid_rbb_before,   valid_rbb_after,   valid_sbb, valid_pubkey,   valid_sv_proof);
   expect_check_shuffle (tc, 0, valid_rbb_before, invalid_rbb_after,   valid_sbb, valid_pubkey,   valid_sv_proof);
   expect_check_shuffle (tc, 0, valid_rbb_before,   valid_rbb_after, invalid_sbb, valid_pubkey,   valid_sv_proof);
   expect_check_shuffle (tc, 0, valid_rbb_before,   valid_rbb_after,   valid_sbb, valid_pubkey, invalid_sv_proof);
}
