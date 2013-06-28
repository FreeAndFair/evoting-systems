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
#include "vhti/combine_dictionary_secrets.h"
#include <stdio.h>
#include <malloc.h>

static void
expect_combine_dictionary_secrets (CuTest *tc,
                                   int expected_status,
                                   TrusteeRevealedDictionarySecrets trustee_dict_secrets_box,
                                   BlankBallot blank_ballot,
                                   int v_len,
                                   AlphabetEncoding v_alphabet)
{
   char *verification_dictionaries = 0;

   CuAssert (tc,
             (0 == expected_status
              ? "VHTI_combine_dictionary_secrets of valid inputs should have succeeded"
              : "VHTI_combine_dictionary_secrets of invalid inputs should have failed"),
             expected_status == VHTI_combine_dictionary_secrets
             ( trustee_dict_secrets_box, blank_ballot, v_len,
               v_alphabet, &verification_dictionaries));

   if (0 != expected_status)
   {
      if (verification_dictionaries) {
         fprintf (stderr, "Hmm: `%s'\n", verification_dictionaries);
      }
      CuAssertPtrEquals (tc, NULL, verification_dictionaries);
   }
   else
   {
      CuAssertPtrNotNull (tc, verification_dictionaries);
      CuAssert (tc, "VHTI_combine_dictionary_secrets should have returned a VoteVerificationDictionaries.",
                0 == (VHTI_validate (VOTE_VERIFICATION_DICTIONARIES, verification_dictionaries)));
      
      VHTI_free (verification_dictionaries);
      verification_dictionaries = 0;
   }
}

void
combine_dictionary_secrets_validation (CuTest *tc)
{
   expect_combine_dictionary_secrets (tc, 0, valid_trustee_dict_secrets_box,
      valid_bb, 32, valid_encoding);
   expect_combine_dictionary_secrets (tc, -1, invalid_trustee_dict_secrets_box,
      valid_bb, 32, valid_encoding);
   expect_combine_dictionary_secrets (tc, -1, valid_trustee_dict_secrets_box,
      invalid_bb, 32, valid_encoding);
   expect_combine_dictionary_secrets (tc, -1, valid_trustee_dict_secrets_box,
      valid_bb, 32, invalid_encoding);
   
}
