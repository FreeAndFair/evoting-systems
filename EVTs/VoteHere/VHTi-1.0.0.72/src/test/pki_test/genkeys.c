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

#include "pki_test.h"
#include <vhti/genkeys.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_null (CuTest *tc,
             const char *to_be_tested,
             const char *description)
{
   if (to_be_tested)
      fprintf (stderr, "Hmm: %s isn't NULL: `%s'\n",
               description,
               to_be_tested);
   CuAssertPtrEquals (tc, NULL, (char *) to_be_tested);
}

static void
expect_valid (CuTest *tc,
              const char *to_be_tested,
              const char *element_type)
{
   char whine[1000];

   CuAssertPtrNotNull (tc, (char *) to_be_tested);
   sprintf (whine,
            "VHTI_generate_keys should have returned a %s",
            element_type);
   CuAssert (tc,
             whine,
             0 == VHTI_validate (element_type, to_be_tested));
}

static void
expect_generate_keys (CuTest *tc,
                      const int expected_status,
                      IdentInfo const ident_info)
{
   char * priv = 0;
   char * pub  = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_generate_keys should have accepted valid input"
              : "VHTI_generate_keys should have rejected invalid input"),
             expected_status == VHTI_generate_keys (ident_info,
                                                    &priv,
                                                    &pub));

   if (0 != expected_status)
   {
      expect_null (tc, priv, GENERAL_PURPOSE_PRIVATE_KEY);
      expect_null (tc, pub , GENERAL_PURPOSE_PUBLIC_KEY );
   }
   else
   {
      expect_valid (tc, priv, GENERAL_PURPOSE_PRIVATE_KEY);
      expect_valid (tc, pub , GENERAL_PURPOSE_PUBLIC_KEY );

      VHTI_free (priv);
      VHTI_free (pub);
   }
}

void
generate_keys_validation (CuTest *tc)
{
   expect_generate_keys (tc, 0, valid_ident_info);
   expect_generate_keys (tc, -1, invalid_ident_info);
}
