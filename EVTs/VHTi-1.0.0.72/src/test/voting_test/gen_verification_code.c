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
#include "vhti/gen_verification_code.h"
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_gen_vvcode (CuTest *tc,
                   const int expected_status,
                   VoteVerificationKeys vv_keys,
                   BlankBallot blank_ballot,
                   BallotSequenceNumber bsn,
                   AnswerReference answer_ref,
                   int vv_len,
                   AlphabetEncoding vv_alphabet)
{
   char * vv_code = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_verification_code should have accepted valid input"
              : "VHTI_generate_verification_code should have rejected invalid input"),
             expected_status
             == VHTI_generate_verification_code (vv_keys, blank_ballot, bsn, answer_ref,
             vv_len, vv_alphabet, &vv_code));

   if (0 != expected_status)
   {
      if (vv_code)
         fprintf (stderr, "Hmm: `%s'\n", vv_code);
      CuAssertPtrEquals (tc, NULL, vv_code);
   }
   else
   {
      CuAssertPtrNotNull (tc, vv_code);
      CuAssert (tc,
                "VHTI_generate_verification_code should have returned a Vote Verification Code.",
                0 == VHTI_validate (VOTE_VERIFICATION_CODE, vv_code) );
      VHTI_free (vv_code);
   }
}

void
gen_vvcode_validation (CuTest *tc)
{
   expect_gen_vvcode (tc, 0, valid_vkeys, valid_bb, valid_bsn, valid_answer_ref, 32, valid_encoding);
   expect_gen_vvcode (tc, -1, invalid_vkeys, valid_bb, valid_bsn, valid_answer_ref, 32, valid_encoding);
   expect_gen_vvcode (tc, -1, valid_vkeys, invalid_bb, valid_bsn, valid_answer_ref, 32, valid_encoding);
   expect_gen_vvcode (tc, -1, valid_vkeys, valid_bb, invalid_bsn, valid_answer_ref, 32, valid_encoding);
   expect_gen_vvcode (tc, -1, valid_vkeys, valid_bb, valid_bsn, invalid_answer_ref, 32, valid_encoding);
   expect_gen_vvcode (tc, -1, valid_vkeys, valid_bb, valid_bsn, valid_answer_ref, 32, invalid_encoding);
}
