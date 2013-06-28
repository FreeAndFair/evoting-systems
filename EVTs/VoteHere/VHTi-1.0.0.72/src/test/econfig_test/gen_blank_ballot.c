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
#include <vhti/gen_blank_ballot.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_generate_blank_ballot (CuTest *tc,
                              const int expected_status,
                              BallotSkeleton ballot_skeleton,
                              CryptoElectionParameters cep,
                              AlphabetEncoding encoding)
{
   char *blank_ballot = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_blank_ballot should have accepted valid input"
              : "VHTI_generate_blank_ballot should have rejected invalid input"),
              expected_status == VHTI_generate_blank_ballot (ballot_skeleton, cep,
              encoding, &blank_ballot));

   if (0 != expected_status)
   {
      if (blank_ballot)
         fprintf (stderr, "Hmm: `%s'\n", blank_ballot);
      CuAssertPtrEquals (tc, NULL, blank_ballot);
   }
   else
   {
      CuAssertPtrNotNull (tc, blank_ballot);

      CuAssert (tc,
                "VHTI_generate_blank_ballot should have returned a BlankBallot",
                0 == ( VHTI_validate (BLANK_BALLOT, blank_ballot))) ;
      VHTI_free (blank_ballot);
   }
}

void
gen_blank_ballot_validation (CuTest *tc)
{
   expect_generate_blank_ballot (tc, 0, valid_ballot_skeleton, valid_ce_parameters,
      valid_encoding);
   expect_generate_blank_ballot (tc, -1, invalid_ballot_skeleton, valid_ce_parameters,
      valid_encoding);
   expect_generate_blank_ballot (tc, -1, valid_ballot_skeleton, invalid_ce_parameters,
      valid_encoding);
   expect_generate_blank_ballot (tc, -1, valid_ballot_skeleton, valid_ce_parameters,
      invalid_encoding);
}
