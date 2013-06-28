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
#include <vhti/gen_seccoeff.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_secret_coefficients (CuTest *tc,
                            const int expected_status,
                            KeyGenParameters const key_gen_parameters,
                            Authority const authority,
                            RandomState const random_state)
{
   char *secret_coefficients = 0;
   char *random_state_out = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_secret_coefficients should have accepted valid input"
              : "VHTI_generate_secret_coefficients should have rejected invalid input"),
             expected_status == VHTI_generate_secret_coefficients (key_gen_parameters,
             authority, random_state, &secret_coefficients, &random_state_out));

   if (0 != expected_status)
   {
      if (secret_coefficients)
         fprintf (stderr, "Hmm: `%s'\n", secret_coefficients);
      CuAssertPtrEquals (tc, NULL, secret_coefficients);

      if (random_state_out)
         fprintf (stderr, "Hmm: `%s'\n", random_state_out);
      CuAssertPtrEquals (tc, NULL, random_state_out);
   }
   else
   {
      CuAssertPtrNotNull (tc, secret_coefficients);
      CuAssertPtrNotNull (tc, random_state_out);
      CuAssert (tc,
         "VHTI_generate_secret_coefficients should have returned a SecretCoefficients and a RandomState",
         0 == (VHTI_validate (SECRET_COEFFICIENTS, secret_coefficients)
         && VHTI_validate (RANDOM_STATE, random_state_out) ) );
      VHTI_free (secret_coefficients);
      VHTI_free (random_state_out);
   }
}

void
gen_seccoeff_validation (CuTest *tc)
{
   expect_secret_coefficients (tc, 0, valid_key_gen_parameters, valid_authority, valid_random_state);
   expect_secret_coefficients (tc, -1, invalid_key_gen_parameters, valid_authority, valid_random_state);
   expect_secret_coefficients (tc, -1, valid_key_gen_parameters, invalid_authority, valid_random_state);
   expect_secret_coefficients (tc, -1, valid_key_gen_parameters, valid_authority, invalid_random_state);
}
