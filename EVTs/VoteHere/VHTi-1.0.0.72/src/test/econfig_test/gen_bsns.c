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
#include "vhti/gen_bsns.h"
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_gen_bsns (CuTest *tc,
                 const int expected_status,
                 ElectionID eid,
                 PrecinctID pid,
                 int numAuthorized,
                 int numProvisional,
                 RandomState random_state)
{
   char * authorized_bsns = 0;
   char * provisional_bsns = 0;
   char * random_state_out = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_bsns should have accepted valid input"
              : "VHTI_generate_bsns should have rejected invalid input"),
             expected_status
             == VHTI_generate_bsns (eid, pid, numAuthorized, numProvisional, random_state,
             &authorized_bsns, &provisional_bsns, &random_state_out));

   if (0 != expected_status)
   {
      if (authorized_bsns)
         fprintf (stderr, "Hmm: `%s'\n", authorized_bsns);
      CuAssertPtrEquals (tc, NULL, authorized_bsns);

      if (provisional_bsns)
         fprintf (stderr, "Hmm: `%s'\n", provisional_bsns);
      CuAssertPtrEquals (tc, NULL, provisional_bsns);

      if (random_state_out)
         fprintf (stderr, "Hmm: `%s'\n", random_state_out);
      CuAssertPtrEquals (tc, NULL, random_state_out);
   }
   else
   {
      CuAssertPtrNotNull (tc, authorized_bsns);
      CuAssertPtrNotNull (tc, provisional_bsns);
      CuAssertPtrNotNull (tc, random_state_out);
      CuAssert (tc,
                "VHTI_generate_bsns should have returned signed Authorized BSNs, Provisional BSNs, and a Random State.",
                0 == (VHTI_validate (BALLOT_SEQUENCE_NUMBERS, authorized_bsns) 
                && VHTI_validate (BALLOT_SEQUENCE_NUMBERS, provisional_bsns)
                && VHTI_validate (RANDOM_STATE, random_state_out) ) );
      VHTI_free (authorized_bsns);
      VHTI_free (provisional_bsns);
      VHTI_free (random_state_out);
   }
}

void
gen_bsns_validation (CuTest *tc)
{
   expect_gen_bsns (tc, 0, valid_election_id, valid_precinct_id, 10, 5, valid_random_state);
   expect_gen_bsns (tc, -1, invalid_election_id, valid_precinct_id, 10, 5, valid_random_state);
   expect_gen_bsns (tc, -1, valid_election_id, invalid_precinct_id, 10, 5, valid_random_state);
   expect_gen_bsns (tc, -1, valid_election_id, valid_precinct_id, 10, 5, invalid_random_state);
}
