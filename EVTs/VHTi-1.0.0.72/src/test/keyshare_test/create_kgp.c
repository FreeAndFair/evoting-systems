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
#include <stdio.h>
#include "keyshare_test.h"
#include <vhti/keyshare_util.h>
#include <support_test/test-data.h>

static void
expect_create_keygen_parameters (CuTest *tc,
                                 const int expected_status,
                                 SeedParameters input_parameters,
                                 RandomState random_state)
{
   char * output_parameters = NULL;
   char * random_state_out = NULL;
   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_create_keygen_parameters should have accepted valid input"
              :"VHTI_create_keygen_parameters should have rejected invalid input"),
             expected_status
             == VHTI_create_keygen_parameters(input_parameters,
                                              random_state,
                                              &output_parameters,
                                              &random_state_out));
   if (0 != expected_status)
   {
      CuAssertPtrEquals (tc, NULL, output_parameters);
      CuAssertPtrEquals (tc, NULL, random_state_out);
   }
   else
   {
      CuAssertPtrNotNull (tc, output_parameters);
      CuAssertPtrNotNull (tc, random_state_out);
      CuAssert (tc,
                "VHTI_create_keygen_parameters should have returned a KeyGenParameters and a RandomState",
                0 == (VHTI_validate (KEY_GEN_PARAMETERS, output_parameters)
                      && VHTI_validate (RANDOM_STATE, random_state_out)));
      VHTI_free (output_parameters);
      VHTI_free (random_state_out);
   }
}

void
create_keygen_parameters_validation (CuTest *tc)
{
   expect_create_keygen_parameters (tc,  0,   valid_seed_parameters,   valid_random_state);
   expect_create_keygen_parameters (tc, -1, invalid_seed_parameters,   valid_random_state);
   expect_create_keygen_parameters (tc, -1,   valid_seed_parameters, invalid_random_state);
}
