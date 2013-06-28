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
#include "vhti/auth.h"
#include <stdio.h>
#include <malloc.h>
#include "support_test/test-data.h"

static void
expect_authentic (CuTest *tc,
                  const int expected_status,
                  SignedVotedBallot const svbs,
                  VoterRoll const vr,
                  BlankBallot const bb)
{
   char *raw_ballot_box = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_authenticate should have accepted valid input"
              : "VHTI_authenticate should have rejected invalid input"),
             expected_status == VHTI_authenticate (svbs, vr, bb, &raw_ballot_box));

   if (0 != expected_status)
   {
      if (raw_ballot_box)
         fprintf (stderr, "Hmm: `%s'\n", raw_ballot_box);
      CuAssertPtrEquals (tc, NULL, raw_ballot_box);
   }
   else
   {
      CuAssertPtrNotNull (tc, raw_ballot_box);
      CuAssert (tc,
                "VHTI_authenticate should have returned a RawBallotBox",
                0 == VHTI_validate (RAW_BALLOT_BOX, raw_ballot_box));
      VHTI_free (raw_ballot_box);
   }
}

void
auth_validation (CuTest *tc)
{
   expect_authentic (tc, 0, valid_svbs,  valid_vr,       valid_bb      );
   expect_authentic (tc, -1, invalid_svb, valid_vr,       valid_bb      );
   expect_authentic (tc, -1, valid_svbs,  invalid_vr,     valid_bb      );
   expect_authentic (tc, -1, valid_svbs,  valid_vr,       invalid_bb);
}
