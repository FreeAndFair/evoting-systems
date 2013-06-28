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
#include <vhti/crypt.h>
#include <stdio.h>
#include <malloc.h>
#include <support_test/test-data.h>

/* call VHTI_free on *encrypted_data if it's not NULL */
static void
expect_encrypt (CuTest *tc,
                const int expected_status,
                const char *const pubkey,
                ConstCharStar const plaintext,
                EncryptedData *encrypted_data)
{
   *encrypted_data = NULL;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_encrypt should have accepted valid input"
              : "VHTI_encrypt should have rejected invalid input"),
             expected_status == VHTI_encrypt (pubkey, plaintext, encrypted_data));

   if (0 != expected_status)
   {
      if (*encrypted_data)
         fprintf (stderr, "Hmm: `%s'\n", *encrypted_data);
      CuAssertPtrEquals (tc, NULL, (char *)*encrypted_data);
   }
   else
   {
      CuAssertPtrNotNull (tc, (char *)*encrypted_data);
      CuAssert (tc,
                "VHTI_encrypt should have returned an EncryptedData blob",
                0 == VHTI_validate (ENCRYPTED_DATA, *encrypted_data));
   }
}

static void
expect_decrypt (CuTest *tc,
                const int expected_status,
                const char *const prvkey,
                const char *const encrypted_data)
{
   char *plaintext = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_decrypt should have accepted valid input"
              : "VHTI_decrypt should have rejected invalid input"),
             expected_status == VHTI_decrypt (prvkey, encrypted_data, &plaintext));

   if (0 != expected_status)
   {
      if (plaintext)
         fprintf (stderr, "Hmm: `%s'\n", plaintext);
      CuAssertPtrEquals (tc, NULL, plaintext);
   }
   else
   {
      CuAssertPtrNotNull (tc, plaintext);
      free (plaintext);
   }
}

void
encrypt_validation (CuTest *tc)
{
   EncryptedData valid_encrypted_data = NULL;

   expect_encrypt (tc, 0, valid_pubkey, valid_XML_plaintext, &valid_encrypted_data);
   expect_encrypt (tc, 0, valid_pubkey, valid_non_XML_plaintext, &valid_encrypted_data);
   expect_decrypt (tc, 0, valid_prvkey, valid_encrypted_data);
   expect_decrypt (tc, -1, valid_prvkey, invalid_encrypted_data);

   VHTI_free (valid_encrypted_data);
}

static void
expect_password_encrypt (CuTest *tc,
                const int expected_status,
                Password const password,
                ConstCharStar const plaintext,
                EncryptedData *encrypted_data)
{
   *encrypted_data = NULL;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_password_encrypt should have accepted valid input"
              : "VHTI_password_encrypt should have rejected invalid input"),
             expected_status == VHTI_password_encrypt (password, plaintext, encrypted_data));

   if (0 != expected_status)
   {
      if (*encrypted_data)
         fprintf (stderr, "Hmm: `%s'\n", *encrypted_data);
      CuAssertPtrEquals (tc, NULL, (char *)*encrypted_data);
   }
   else
   {
      CuAssertPtrNotNull (tc, (char *)*encrypted_data);
      CuAssert (tc,
                "VHTI_password_encrypt should have returned an EncryptedData blob",
                0 == VHTI_validate (PASSWORD_ENCRYPTED_DATA, *encrypted_data));
   }
}

static void
expect_password_decrypt (CuTest *tc,
                const int expected_status,
                Password const password,
                PasswordEncryptedData const encrypted_data)
{
   char *plaintext = 0;

   CuAssert (tc,
             (0 == expected_status ?
              "VHTI_password_decrypt should have accepted valid input"
              : "VHTI_password_decrypt should have rejected invalid input"),
             expected_status == VHTI_password_decrypt (password, encrypted_data, &plaintext));

   if (0 != expected_status)
   {
      if (plaintext)
         fprintf (stderr, "Hmm: `%s'\n", plaintext);
      CuAssertPtrEquals (tc, NULL, plaintext);
   }
   else
   {
      CuAssertPtrNotNull (tc, plaintext);
      free (plaintext);
   }
}

void
password_encrypt_validation (CuTest *tc)
{
   PasswordEncryptedData valid_encrypted_data = NULL;
   ConstCharStar const valid_pw_plaintext = "Hello World with a password";

   expect_password_encrypt (tc, 0, valid_password, valid_pw_plaintext, &valid_encrypted_data);
   expect_password_encrypt (tc, 0, valid_password, valid_non_XML_plaintext, &valid_encrypted_data);
   expect_password_encrypt (tc, -1, invalid_password, valid_pw_plaintext, &valid_encrypted_data);

   VHTI_free (valid_encrypted_data);
}

void
password_decrypt_validation (CuTest *tc)
{
   expect_password_decrypt (tc, 0, valid_password, valid_pw_encrypted_data);
   expect_password_decrypt (tc, -1, invalid_password, valid_pw_encrypted_data);
   expect_password_decrypt (tc, -1, valid_password, invalid_pw_encrypted_data);
}


