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
#include "vhti/sign_receipt.h"
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_sign_receipt (CuTest *tc,
                     const int expected_status,
                     VoteReceiptData vote_receipt_data,
                     GeneralPurposePrivateKey receipt_signing_key)
{
   char * vote_receipt = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_sign_receipt should have accepted valid input"
              : "VHTI_sign_receipt should have rejected invalid input"),
             expected_status == VHTI_sign_receipt (vote_receipt_data, 
             receipt_signing_key, &vote_receipt));

   if (0 != expected_status)
   {
      if (vote_receipt)
         fprintf (stderr, "Hmm: `%s'\n", vote_receipt);
      CuAssertPtrEquals (tc, NULL, vote_receipt);
   }
   else
   {
      CuAssertPtrNotNull (tc, vote_receipt);
      CuAssert (tc,
                "VHTI_sign_receipt should have returned a Vote Receipt.",
                0 == VHTI_validate (SIGNED_VOTE_RECEIPT_DATA, vote_receipt) );
      VHTI_free (vote_receipt);
   }
}

void
sign_receipt_validation (CuTest *tc)
{
   expect_sign_receipt (tc,  0,   valid_vote_receipt_data,   valid_prvkey);
   expect_sign_receipt (tc, -1, invalid_vote_receipt_data,   valid_prvkey);
   expect_sign_receipt (tc, -1,   valid_vote_receipt_data, invalid_prvkey);
}
