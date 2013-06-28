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
#include "vhti/check_pds_and_combine.h"
#include <stdio.h>
#include <string.h>
#include <malloc.h>

static void
expect_combine_partial_decrypt (CuTest *tc,
                                int expected_status,
                                SignedBlankBallot signed_blank_ballot,
                                GeneralPurposePublicKey ballot_signing_key,
                                PartiallyDecryptedBallotBox pd_ballot_box)
{
   char *clear_text_ballots = 0;
   char *combine_partial_decrypt_result = 0;

   CuAssert (tc,
      (0 == expected_status
      ? "VHTI_check_partial_decrypts_and_combine of valid inputs should have succeeded"
      : "VHTI_check_partial_decrypts_and_combine of invalid inputs should have failed"),
      expected_status == VHTI_check_partial_decrypts_and_combine
             (signed_blank_ballot, ballot_signing_key,
              pd_ballot_box,
              &clear_text_ballots, &combine_partial_decrypt_result));
   
   if (0 != expected_status)
   {
      if (clear_text_ballots) {
         fprintf (stderr, "Hmm: `%s'\n", clear_text_ballots);
      }
      CuAssertPtrEquals (tc, NULL, clear_text_ballots);

      if (combine_partial_decrypt_result) {
         fprintf (stderr, "Hmm: `%d'\n", combine_partial_decrypt_result);
      }
      CuAssertPtrEquals (tc, NULL, combine_partial_decrypt_result);
   }
   else
   {
      CuAssertPtrNotNull (tc, clear_text_ballots);
      CuAssertPtrNotNull (tc, combine_partial_decrypt_result);
      CuAssert (tc, "VHTI_check_partial_decrypts_and_combine should have returned clear_text_ballots.",
         0 == (VHTI_validate (CLEAR_TEXT_BALLOTS, clear_text_ballots)));
      //|| VHTI_validate (COMBINE_PARTIAL_DECRYPT_RESULT, combine_partial_decrypt_result)));
      VHTI_free (clear_text_ballots);
      VHTI_free (combine_partial_decrypt_result);
      
      clear_text_ballots = 0;
      combine_partial_decrypt_result = 0;
   }
}

void
combine_partial_decrypts_validation (CuTest *tc)
{
   expect_combine_partial_decrypt (tc,  0,   valid_sbb, valid_pubkey,   valid_pd_ballot_box);
   expect_combine_partial_decrypt (tc, -1, invalid_sbb, valid_pubkey,   valid_pd_ballot_box);
   expect_combine_partial_decrypt (tc, -1,   valid_sbb, valid_pubkey, invalid_pd_ballot_box);
}
