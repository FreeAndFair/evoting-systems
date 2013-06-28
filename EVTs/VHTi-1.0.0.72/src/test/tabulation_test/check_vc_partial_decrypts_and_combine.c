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
#include "vhti/check_vc_pds_and_combine.h"
#include <stdio.h>
#include <string.h>
#include <malloc.h>

static void
expect_check_vc_partial_decrypts_and_combine (CuTest *tc,
                                              int expected_status,
                                              PreVerificationCodeBoxes const pre_vcode_boxes,
                                              AuthorityPartialDecrypts const auth_partial_decrypts,
                                              SignedVotedBallots signed_voted_ballots,
                                              SignedBlankBallot const signed_blank_ballot,
                                              GeneralPurposePublicKey ballot_signing_key,
                                              int v_len,
                                              AlphabetEncoding v_alphabet)
{
   char *vv_statements = 0;
   char *combine_partial_decrypt_result = 0;

   CuAssert (tc,
             (0 == expected_status
              ? "VHTI_check_vcode_partial_decrypts_and_combine of valid inputs should have succeeded"
              : "VHTI_check_vcode_partial_decrypts_and_combine of invalid inputs should have failed"),
             expected_status == VHTI_check_vcode_partial_decrypts_and_combine
             ( pre_vcode_boxes,
               auth_partial_decrypts, signed_voted_ballots,
               signed_blank_ballot, ballot_signing_key,
               v_len, v_alphabet,
               &vv_statements, &combine_partial_decrypt_result));

   if (0 != expected_status)
   {
      if (vv_statements) {
         fprintf (stderr, "Hmm: `%s'\n", vv_statements);
      }
      CuAssertPtrEquals (tc, NULL, vv_statements);

      if (combine_partial_decrypt_result) {
         fprintf (stderr, "Hmm: `%s'\n", combine_partial_decrypt_result);
      }
      CuAssertPtrEquals (tc, NULL, combine_partial_decrypt_result);
   }
   else
   {
      CuAssertPtrNotNull (tc, vv_statements);
      CuAssertPtrNotNull (tc, combine_partial_decrypt_result);
      CuAssert (tc, "VHTI_check_vcode_partial_decrypts_and_combine should have returned VoteVerificationStatements and CheckResults.",
                0 == (VHTI_validate (VOTE_VERIFICATION_STATEMENTS, vv_statements)
                || VHTI_validate (CHECK_RESULTS, combine_partial_decrypt_result)));
      
      
      VHTI_free (vv_statements);
      vv_statements = 0;
      VHTI_free (combine_partial_decrypt_result);
      combine_partial_decrypt_result = 0;
   }
}

void
check_vc_partial_decrypts_and_combine_validation (CuTest *tc)
{
   expect_check_vc_partial_decrypts_and_combine (tc,  0,   valid_pvc_boxes,   valid_auth_pds_4vc,   valid_svbs,   valid_sbb, valid_pubkey, 32,   valid_encoding);
   expect_check_vc_partial_decrypts_and_combine (tc, -1, invalid_pvc_boxes,   valid_auth_pds_4vc,   valid_svbs,   valid_sbb, valid_pubkey, 32,   valid_encoding);
   expect_check_vc_partial_decrypts_and_combine (tc, -1,   valid_pvc_boxes, invalid_auth_pds_4vc,   valid_svbs,   valid_sbb, valid_pubkey, 32,   valid_encoding);
   expect_check_vc_partial_decrypts_and_combine (tc, -1,   valid_pvc_boxes,   valid_auth_pds_4vc, invalid_svbs,   valid_sbb, valid_pubkey, 32,   valid_encoding);
   expect_check_vc_partial_decrypts_and_combine (tc, -1,   valid_pvc_boxes,   valid_auth_pds_4vc,   valid_svbs, invalid_sbb, valid_pubkey, 32,   valid_encoding);
   expect_check_vc_partial_decrypts_and_combine (tc, -1,   valid_pvc_boxes,   valid_auth_pds_4vc,   valid_svbs,   valid_sbb, valid_pubkey, 32, invalid_encoding);
}
