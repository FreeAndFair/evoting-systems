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
#include <vhti/sign.h>
#include <stdio.h>
#include <string.h>
#include <malloc.h>
#include <support_test/test-data.h>

static void
expect_sign (CuTest *tc,
             const int expected_status,
             GeneralPurposePrivateKey const prvkey,
             ConstCharStar const plaintext)
{
   char *signature = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_sign should have accepted valid input"
              : "VHTI_sign should have rejected invalid input"),
             expected_status == VHTI_sign (prvkey, plaintext, &signature));

   if (0 != expected_status)
   {
      if (signature)
         fprintf (stderr, "Hmm: `%s'\n", signature);
      CuAssertPtrEquals (tc, NULL, signature);
   }
   else
   {
      CuAssertPtrNotNull (tc, signature);
      CuAssert (tc,
                "VHTI_sign should have returned a Signature",
                0 == VHTI_validate (SIGNATURE, signature));
      VHTI_free (signature);
   }
}

void
sign_validation (CuTest *tc)
{
   expect_sign (tc, 0, valid_prvkey, valid_non_XML_plaintext);
   expect_sign (tc, 0, valid_prvkey, valid_XML_plaintext);
}

static void
expect_verify_signature (CuTest *tc,
                         const int expected_status,
                         GeneralPurposePublicKey const pubkey,
                         ConstCharStar const plaintext,
                         Signature const signature)
{
   char * c_res;
   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_verify_signature should have accepted valid input"
              : "VHTI_verify_signature should have rejected invalid input"),
             expected_status == VHTI_verify_signature (pubkey, plaintext, signature, &c_res));
              
   if (0 != expected_status)
   {
      if (c_res)
         fprintf (stderr, "Hmm: `%s'\n", c_res);
      CuAssertPtrEquals (tc, NULL, c_res);
   }
   else
   {
      CuAssertPtrNotNull (tc, c_res);
      CuAssert (tc,
                "VHTI_sign should have returned a CheckResults object",
                0 == VHTI_validate (CHECK_RESULTS, c_res));
      VHTI_free (c_res);
   }
}

void
verify_signature_validation (CuTest *tc)
{
   expect_verify_signature (tc, 0, valid_pubkey, valid_non_XML_plaintext, valid_signature);
   expect_verify_signature (tc, 0, valid_pubkey, valid_XML_plaintext, valid_signature);
   expect_verify_signature (tc, -1, valid_pubkey, valid_non_XML_plaintext, invalid_signed_document);
   expect_verify_signature (tc, -1, valid_pubkey, valid_XML_plaintext, invalid_signed_document);
}
