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

#include "voting_test.h"
#include "vhti/enc_ballot_pollsite.h"
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_encrypt_ballot_pollsite (CuTest *tc,
                                const int expected_status,
                                ClearTextBallot clear_text_ballot,
                                BlankBallot blank_ballot,
                                BallotSequenceNumber bsn,
                                RandomState random_state,
                                GeneralPurposePrivateKey ballot_signing_key)
{
   char * signed_voted_ballot = 0;
   char * random_state_out = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_encrypt_ballot_pollsite should have accepted valid input"
              : "VHTI_encrypt_ballot_pollsite should have rejected invalid input"),
             expected_status
             == VHTI_encrypt_ballot_pollsite (clear_text_ballot, blank_ballot, bsn,
                                     random_state, ballot_signing_key,
                                     &signed_voted_ballot, &random_state_out));

   if (0 != expected_status)
   {
      if (signed_voted_ballot)
         fprintf (stderr, "Hmm: `%s'\n", signed_voted_ballot);
      CuAssertPtrEquals (tc, NULL, signed_voted_ballot);

      if (random_state_out)
         fprintf (stderr, "Hmm: `%s'\n", random_state_out);
      CuAssertPtrEquals (tc, NULL, random_state_out);
   }
   else
   {
      CuAssertPtrNotNull (tc, signed_voted_ballot);
      CuAssertPtrNotNull (tc, random_state_out);
      CuAssert (tc,
                "VHTI_encrypt_ballot_pollsite should have returned a signed Voted Ballot and a Random State.",
                0 == (VHTI_validate (SIGNED_VOTED_BALLOT, signed_voted_ballot) 
                && VHTI_validate (RANDOM_STATE, random_state_out) ) );
      VHTI_free (signed_voted_ballot);
      VHTI_free (random_state_out);
   }
}

void
encrypt_ballot_pollsite_validation (CuTest *tc)
{
   expect_encrypt_ballot_pollsite (tc, 0, valid_clear_text_ballot, valid_bb, valid_bsn,
      valid_random_state,  valid_prvkey);
   expect_encrypt_ballot_pollsite (tc, -1, invalid_clear_text_ballot, valid_bb, valid_bsn,
      valid_random_state,  valid_prvkey);
   expect_encrypt_ballot_pollsite (tc, -1, valid_clear_text_ballot, invalid_bb, valid_bsn,
      valid_random_state,  valid_prvkey);
   expect_encrypt_ballot_pollsite (tc, -1, valid_clear_text_ballot, valid_bb, invalid_bsn,
      valid_random_state,  valid_prvkey);
   expect_encrypt_ballot_pollsite (tc, -1, valid_clear_text_ballot, valid_bb, valid_bsn,
      invalid_random_state,  valid_prvkey);
   expect_encrypt_ballot_pollsite (tc, -1, valid_clear_text_ballot, valid_bb, valid_bsn,
      valid_random_state,  invalid_prvkey);
}
