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
#include "vhti/shuffle.h"
#include <stdio.h>
#include "support_test/test-data.h"
#include "vhti/types.h"
#include <malloc.h>

static void
expect_shuffle (CuTest *tc,
                const int expect_success,
                RawBallotBox const raw_ballot_box_before,
                RandomState const random_state,
                SignedBlankBallot const signed_blank_ballot,
                GeneralPurposePublicKey ballot_signing_key)
{
   char *raw_ballot_box_after = 0;
   char *return_random_state = 0;
   char *shuffle_validity_proof = 0;

   CuAssert (tc,
             (expect_success
              ? "VHTI_shuffle of valid inputs should have succeeded"
              : "VHTI_shuffle of invalid inputs should have failed"),
             ((1 == expect_success)
              ==
              (0 == VHTI_shuffle
               (raw_ballot_box_before,
                random_state,
                signed_blank_ballot, ballot_signing_key,
                &raw_ballot_box_after, &return_random_state, &shuffle_validity_proof))));

   if (!expect_success)
   {
      if (raw_ballot_box_after) {
         fprintf (stderr, "Hmm: `%s'\n", raw_ballot_box_after);
      }
      CuAssertPtrEquals (tc, NULL, raw_ballot_box_after);

      if (return_random_state) {
         fprintf (stderr, "Hmm: `%s'\n", return_random_state);
      }
      CuAssertPtrEquals (tc, NULL, return_random_state);


      if (shuffle_validity_proof) {
         fprintf (stderr, "Hmm: `%s'\n", shuffle_validity_proof);
      }
      CuAssertPtrEquals (tc, NULL, shuffle_validity_proof);
   }
   else
   {
      CuAssertPtrNotNull (tc, raw_ballot_box_after);
      CuAssertPtrNotNull (tc, return_random_state);
      CuAssertPtrNotNull (tc, shuffle_validity_proof);
      CuAssert (tc,
                "VHTI_shuffle should have returned a raw_ballot_box, a random_state, and "
                "a shuffle_validity_proofs object.",
                0 == (VHTI_validate (RAW_BALLOT_BOX, raw_ballot_box_after)
                      || VHTI_validate (SHUFFLE_VALIDITY_PROOF, shuffle_validity_proof)
                      || VHTI_validate (RANDOM_STATE, return_random_state)));
      VHTI_free (raw_ballot_box_after);
      VHTI_free (return_random_state);
      VHTI_free (shuffle_validity_proof);
   }
}

void
shuffle_validation (CuTest *tc)
{
   expect_shuffle (tc, 1,   valid_rbb_before,   valid_random_state,   valid_sbb, valid_pubkey);
   expect_shuffle (tc, 0, invalid_rbb_before,   valid_random_state,   valid_sbb, valid_pubkey);
   expect_shuffle (tc, 0,   valid_rbb_before, invalid_random_state,   valid_sbb, valid_pubkey);
   expect_shuffle (tc, 0,   valid_rbb_before,   valid_random_state, invalid_sbb, valid_pubkey);
}
