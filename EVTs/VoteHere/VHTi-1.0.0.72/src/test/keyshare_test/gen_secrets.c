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

#include "keyshare_test.h"
#include <vhti/gen_secrets.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_generate_secret (CuTest *tc,
                        const int expected_status,
                        KeyGenParameters const key_gen_parameters,
                        Authority const authority,
                        SecretCoefficients const secret_coefficients)
{
   char *pairwise_secret = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_secret should have accepted valid input"
              : "VHTI_generate_secret should have rejected invalid input"),
             expected_status == VHTI_generate_secret (key_gen_parameters, authority,
             secret_coefficients, &pairwise_secret));

   if (0 != expected_status)
   {
      if (pairwise_secret)
         fprintf (stderr, "Hmm: `%s'\n", pairwise_secret);
      CuAssertPtrEquals (tc, NULL, pairwise_secret);
   }
   else
   {
      CuAssertPtrNotNull (tc, pairwise_secret);
      CuAssert (tc,
                "VHTI_generate_secret should have returned a PairwiseSecret blob",
                0 == VHTI_validate (PAIRWISE_SECRET, pairwise_secret));
      VHTI_free (pairwise_secret);
   }
}

void
gen_secrets_validation (CuTest *tc)
{
   expect_generate_secret (tc, 0, valid_key_gen_parameters, valid_authority, valid_secret_coefficients);
   expect_generate_secret (tc, -1, invalid_key_gen_parameters, valid_authority, valid_secret_coefficients);
   expect_generate_secret (tc, -1, valid_key_gen_parameters, invalid_authority, valid_secret_coefficients);
   expect_generate_secret (tc, -1, valid_key_gen_parameters, valid_authority, invalid_secret_coefficients);
}
