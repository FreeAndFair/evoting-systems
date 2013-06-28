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
#include "vhti/check_partial_decrypt.h"
#include <stdio.h>
#include <malloc.h>

static void
expect_check_partial_decrypt (CuTest *tc,
                              int expected_status,
                              RawBallotBox const raw_ballot_box,
                              AuthorityPartialDecrypt const auth_partial_decrypt,
                              SignedBlankBallot const signed_blank_ballot,
                              GeneralPurposePublicKey ballot_signing_key)
{
   char *check_partial_decrypt_result = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_check_partial_decrypt should have accepted valid input"
              : "VHTI_check_partial_decrypt should have rejected invalid input"),
             expected_status == VHTI_check_partial_decrypt
             (raw_ballot_box, auth_partial_decrypt,
              signed_blank_ballot, ballot_signing_key, &check_partial_decrypt_result));

   if (0 != expected_status)
   {
       if (check_partial_decrypt_result)
         fprintf (stderr, "Hmm: `%s'\n", check_partial_decrypt_result);
      CuAssertPtrEquals (tc, NULL, check_partial_decrypt_result);
   }
   else
   {
      CuAssertPtrNotNull (tc, check_partial_decrypt_result);
      CuAssert (tc,
                "VHTI_check_partial_decrypt should have returned CheckResults",
                0 == VHTI_validate (CHECK_RESULTS, check_partial_decrypt_result));
      VHTI_free (check_partial_decrypt_result);
   }
}

void
check_partial_decrypt_validation (CuTest *tc)
{
   expect_check_partial_decrypt (tc,  0,   valid_rbb,   valid_auth_pd,   valid_sbb, valid_pubkey);
   expect_check_partial_decrypt (tc, -1, invalid_rbb,   valid_auth_pd,   valid_sbb, valid_pubkey);
   expect_check_partial_decrypt (tc, -1,   valid_rbb, invalid_auth_pd,   valid_sbb, valid_pubkey);
   expect_check_partial_decrypt (tc, -1,   valid_rbb,   valid_auth_pd, invalid_sbb, valid_pubkey);
}
