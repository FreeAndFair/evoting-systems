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

#include <misc/xml_tree.h>
#include "vhti/types.h"
#include "support/bignum.h"
#include "support_test.h"
#include <sstream>

static void
expect_bignum (CuTest *tc, const char *xml, unsigned expected)
{
   VHUtil::xml_tree xt (xml);
   const BIGNUM *bn = xml2BN (xt.root ());
   BIGNUM bn_expected;
   BN_init     (&bn_expected);
   BN_zero     (&bn_expected);
   BN_set_word (&bn_expected, expected);
   std::string whine;
   {
      std::ostringstream tmp;
      char *expected_str = BN_bn2dec (&bn_expected);
      char *actual_str   = BN_bn2dec (bn);
      tmp << "`" << xml << "' yielded "
          << actual_str
          << ", but expected "
          << expected_str;
      OPENSSL_free (expected_str);
      OPENSSL_free (actual_str);
      whine = tmp.str ();
   }
   CuAssert (tc, (char *) whine.c_str (), 0 == BN_cmp (&bn_expected, bn));
}

#include <iostream>

void
bignums (CuTest *tc)
{
   expect_bignum (tc, "<fred Encoding=\"DEC\">15</fred>", 15);
   expect_bignum (tc, "<fred>15</fred>", 15);
   expect_bignum (tc, "<fred Encoding=\"HEX\">f</fred>", 15);
   
   // Lord help us, the library remembers the last encoding.  Since
   // the previous call used HEX, this ought to be read as hex.
   expect_bignum (tc, "<fred>f</fred>", 15);

   bool fCaughtException = false;
   try {
      expect_bignum (tc, "<sam Encoding=\"DEC\">   10 </sam>", 10);
   }
   catch (const VHUtil::Exception &)
   {
      fCaughtException = true;
   }
   CuAssert (tc, "Got expected exception with leading whitespace", fCaughtException);
   
   expect_bignum (tc, "<mary Encoding=\"BASE64\">Kg==</mary>", 42);
}
