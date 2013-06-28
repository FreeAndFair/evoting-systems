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

#include "vhti/permutation.h"
#include "vhti/types.h"
#include "support_test.h"
#include <misc/cutest.h>
#include "support_test/test-data.h"
#include <stdio.h>
#include <malloc.h>

static void
expect_get_permutation (CuTest *tc,
                        int expected_status,
                        RandomState random_state,
                        int nsize)
{
   char *permutation = 0;
   char *return_random_state = 0;

   CuAssert (tc,
      (0 == expected_status
      ? "VHTI_get_permutation of valid inputs should have succeeded"
      : "VHTI_get_permutation of invalid inputs should have failed"),
      expected_status == VHTI_get_permutation(random_state, nsize, &permutation,
      &return_random_state));

   if (0 != expected_status)
   {
      if (permutation) {
         fprintf (stderr, "Hmm: `%s'\n", permutation);
      }
      CuAssertPtrEquals (tc, NULL, permutation);
   }
   else
   {
      CuAssertPtrNotNull (tc, permutation);
      CuAssert (tc, "VHTI_get_permutation should have returned a permutation "
                    "and a random_state.",
         0 == (VHTI_validate (PERMUTATION, permutation)
         || VHTI_validate (RANDOM_STATE, return_random_state)));

      VHTI_free (permutation);
      VHTI_free (return_random_state);
   }
}

void
get_permutation_validation (CuTest *tc)
{
   expect_get_permutation (tc, 0, valid_random_state, 10);
   expect_get_permutation (tc, -1, invalid_random_state, 10);
}
