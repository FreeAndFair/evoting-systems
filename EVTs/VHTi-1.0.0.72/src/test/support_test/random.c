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

#include "vhti/random.h"
#include "vhti/types.h"
#include "support_test.h"
#include <misc/cutest.h>
#include "support_test/test-data.h"
#include <stdio.h>
#include <malloc.h>

static void
expect_get_bits (CuTest *tc,
                 int expected_status,
                 RandomState random_state,
                 int nbits)
{
   char *return_random_state = 0;
   char *bits = 0;

   CuAssert (tc,
      (0 == expected_status
      ? "VHTI_get_bits of valid inputs should have succeeded"
      : "VHTI_get_bits of invalid inputs should have failed"),
      expected_status == VHTI_get_bits(random_state, nbits, &return_random_state,
      &bits));
   
   if (0 != expected_status)
   {
      if (return_random_state) {
         fprintf (stderr, "Hmm: `%s'\n", return_random_state);
      }
      CuAssertPtrEquals (tc, NULL, return_random_state);
      
      if (bits) {
         fprintf (stderr, "Hmm: `%d'\n", bits);
      }
      CuAssertPtrEquals (tc, NULL, bits);
   }
   else
   {
      CuAssertPtrNotNull (tc, return_random_state);
      CuAssertPtrNotNull (tc, bits);
      CuAssert (tc, "VHTI_get_bits should have returned return_random_state and bits.",
         0 == (VHTI_validate (RANDOM_STATE, return_random_state)
         && VHTI_validate (RANDOM_BITS, bits)));
      VHTI_free (return_random_state);
      VHTI_free (bits);
      
      return_random_state = 0;
      bits = 0;
   }
}

void
get_bits_validation (CuTest *tc)
{
   expect_get_bits (tc, 0, valid_random_state, 7);
   expect_get_bits (tc, 1, invalid_random_state, 7);
}

