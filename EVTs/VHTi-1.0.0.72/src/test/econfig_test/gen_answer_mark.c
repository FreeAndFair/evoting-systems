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

#include "econfig_test.h"
#include <vhti/gen_answer_mark.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_generate_answer_mark (CuTest *tc,
                             const int expected_status,
                             CryptoGroupParameters crypto_group_parameters,
                             AlphabetEncoding encoding,
                             RandomState random_state)
{
   char *answer_mark = 0;
   char *ending_random_state = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_answer_mark should have accepted valid input"
              : "VHTI_generate_answer_mark should have rejected invalid input"),
             expected_status == VHTI_generate_answer_mark (crypto_group_parameters, encoding,
             random_state, &answer_mark, &ending_random_state));

   if (0 != expected_status)
   {
      if (answer_mark)
         fprintf (stderr, "Hmm: `%s'\n", answer_mark);
      CuAssertPtrEquals (tc, NULL, answer_mark);

      if (ending_random_state)
         fprintf (stderr, "Hmm: `%s'\n", ending_random_state);
      CuAssertPtrEquals (tc, NULL, ending_random_state);
   }
   else
   {
      CuAssertPtrNotNull (tc, answer_mark);
      CuAssertPtrNotNull (tc, ending_random_state);
      CuAssert (tc,
                "VHTI_generate_answer_mark should have returned an AnswerMark and a RandomState",
                0 == ( VHTI_validate (ANSWER_MARK, answer_mark)
                && VHTI_validate (RANDOM_STATE, ending_random_state) ) );
      VHTI_free (answer_mark);
      VHTI_free (ending_random_state);
   }
}

void
gen_answer_mark_validation (CuTest *tc)
{
   expect_generate_answer_mark (tc, 0, valid_cg_parameters, valid_encoding, valid_random_state);
   expect_generate_answer_mark (tc, -1, invalid_cg_parameters, valid_encoding, valid_random_state);
   expect_generate_answer_mark (tc, -1, valid_cg_parameters, invalid_encoding, valid_random_state);
   expect_generate_answer_mark (tc, -1, valid_cg_parameters, valid_encoding, invalid_random_state);
}