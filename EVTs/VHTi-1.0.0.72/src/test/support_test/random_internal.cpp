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

#include "support/random_internal.h"
#include "vhti/types.h"
#include "support/bignum.h"
#include "support_test.h"
#include "util/sslerror.h"
#include <misc/cutest.h>
#include "support_test/test-data.h"
#include <stdio.h>
#include <malloc.h>
#include <iostream>

static void
expect_get_ij_bits (CuTest *tc,
                    int expect_exception,
                    RandomIJState random_ij_state,
                    auto_BN i_index,
                    auto_BN j_index,
                    int nbits)
{
   auto_freeing <RandomIJState> return_random_ij_state = 0;
   auto_freeing <RandomBits>    bits = 0;

   bool fCaughtException = false;
   try {
      VHInternal::get_ij_bits (random_ij_state,
                               i_index,
                               j_index,
                               nbits,
                               &return_random_ij_state,
                               &bits);
   } catch (VHUtil::Exception &) {
      fCaughtException = true;
   }
   
   CuAssert (tc,
             (expect_exception
              ? "get_ij_bits of valid inputs should have succeeded"
              : "get_ij_bits of invalid inputs should have failed"),
             expect_exception == (fCaughtException ? 1 : 0));
   
   if (0 != expect_exception)
   {
      if (return_random_ij_state) {
         fprintf (stderr, "Hmm: `%s'\n", static_cast<const char *>(return_random_ij_state));
      }
      CuAssertPtrEquals (tc, NULL, return_random_ij_state);
      
      if (bits) {
         fprintf (stderr, "Hmm: `%d'\n", static_cast<const char *>(bits));
      }
      CuAssertPtrEquals (tc, NULL, bits);
   }
   else
   {
      CuAssertPtrNotNull (tc, return_random_ij_state);
      CuAssertPtrNotNull (tc, bits);
      CuAssert (tc, "get_ij_bits should have returned return_random_ij_state and bits.",
                0 == (VHTI_validate (RANDOM_IJ_STATE, return_random_ij_state)
                      && VHTI_validate (RANDOM_BITS, bits)));
   }
}

void
get_ij_bits_validation (CuTest *tc)
{
   auto_BN i_index;
   auto_BN j_index;
   VH_nonzero (BN_zero(i_index), SSL_ERROR);
   VH_nonzero (BN_zero(j_index), SSL_ERROR);

   expect_get_ij_bits (tc, 0, valid_random_ij_state, i_index, j_index, 7);
   expect_get_ij_bits (tc, 1, invalid_random_ij_state, i_index, j_index, 7);
}

// Include the source code directly, so that we can access the
// internal functions.
#include <support/random.cpp>
#include "support_test.h"

void
get_bits_internal_test (CuTest *tc)
{
   unsigned char fips_buffer[PRNG_STATESZ];

   try
   {
      auto_BN key;

      // Make sure the key has some effect on the result

      memset(fips_buffer, '\0', sizeof (fips_buffer));
      auto_BN with_empty_key = VHInternal::get_bits_internal (10 * VHInternal::digest_bits,
                                                              key,
                                                              fips_buffer);

      if (!BN_set_word (key, 1))
         throw SSL_ERROR;
      memset(fips_buffer, '\0', sizeof (fips_buffer));
      auto_BN with_unity_key = VHInternal::get_bits_internal (10 * VHInternal::digest_bits,
                                                              key,
                                                              fips_buffer);

      CuAssert (tc,
                "key has no effect on returned bits",
                0 != BN_cmp (with_empty_key, with_unity_key));

      // Make sure we don't get the same bits twice in a row.
      auto_BN unity_key_take_two = VHInternal::get_bits_internal (10 * VHInternal::digest_bits,
                                                                  key,
                                                                  fips_buffer);
      CuAssert (tc,
                "Got the same bits twice in a row",
                0 != BN_cmp (with_unity_key, unity_key_take_two));

   } catch (const VHUtil::Exception & e) {
      CuAssert (tc, const_cast<char *> (("Exception: " + e.getWhat ()).c_str ()), false);
   }
}
