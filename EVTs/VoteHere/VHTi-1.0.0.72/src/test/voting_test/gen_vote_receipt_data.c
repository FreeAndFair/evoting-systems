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
#include "vhti/gen_vote_receipt_data.h"
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_gen_vote_receipt_data (CuTest *tc,
                              const int expected_status,
                              SignedVotedBallot signed_voted_ballot,
                              VoteVerificationKeys vv_keys,
                              BlankBallot blank_ballot,
                              BallotSequenceNumber bsn,
                              ClearTextBallot clear_text_ballot,
                              int vv_len,
                              AlphabetEncoding vv_alphabet)
{
   char * vote_receipt_data = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_vote_receipt_data should have accepted valid input"
              : "VHTI_generate_vote_receipt_data should have rejected invalid input"),
             expected_status == VHTI_generate_vote_receipt_data (signed_voted_ballot,
             vv_keys, blank_ballot, bsn, clear_text_ballot, vv_len,
             vv_alphabet, &vote_receipt_data));

   if (0 != expected_status)
   {
      if (vote_receipt_data)
         fprintf (stderr, "Hmm: `%s'\n", vote_receipt_data);
      CuAssertPtrEquals (tc, NULL, vote_receipt_data);
   }
   else
   {
      CuAssertPtrNotNull (tc, vote_receipt_data);
      CuAssert (tc,
                "VHTI_generate_vote_receipt_data should have returned Vote Receipt Data.",
                0 == VHTI_validate (VOTE_RECEIPT_DATA, vote_receipt_data) );
      VHTI_free (vote_receipt_data);
   }
}

void
gen_vote_receipt_data_validation (CuTest *tc)
{
   expect_gen_vote_receipt_data (tc, 0, valid_svb, valid_vkeys, valid_bb, valid_bsn, valid_clear_text_ballot,
      32, valid_encoding);
   expect_gen_vote_receipt_data (tc, -1, invalid_svb, valid_vkeys, valid_bb, valid_bsn, valid_clear_text_ballot,
      32, valid_encoding);
   expect_gen_vote_receipt_data (tc, -1, valid_svb, invalid_vkeys, valid_bb, valid_bsn, valid_clear_text_ballot,
      32, valid_encoding);
   expect_gen_vote_receipt_data (tc, -1, valid_svb, valid_vkeys, invalid_bb, valid_bsn, valid_clear_text_ballot,
      32, valid_encoding);
   expect_gen_vote_receipt_data (tc, -1, valid_svb, valid_vkeys, valid_bb, invalid_bsn, valid_clear_text_ballot,
      32, valid_encoding);
   expect_gen_vote_receipt_data (tc, -1, valid_svb, valid_vkeys, valid_bb, valid_bsn, invalid_clear_text_ballot,
      32, valid_encoding);
   expect_gen_vote_receipt_data (tc, -1, valid_svb, valid_vkeys, valid_bb, valid_bsn, valid_clear_text_ballot,
      32, invalid_encoding);
}
