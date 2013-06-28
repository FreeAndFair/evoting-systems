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

#ifndef PKI_MISC_H
#define PKI_MISC_H
#include <vhti/types.h>
#include <string>
#include <support/auto_c_ptr.h>
#include <util/sslerror.h>

class free_BIO {
public:
   static void free(BIO *x)
      {
         BIO_free(x);
      }
};
typedef auto_C_PTR<BIO, free_BIO> auto_BIO;

typedef std::basic_string<unsigned char> ustring;
typedef std::basic_ostringstream<unsigned char> uss;

#define XML_ERROR(text) VHUtil::Exception (__FILE__, __LINE__, ("Unknown XML error parsing " + std::string (text)).c_str ())

ustring
xml_wrap (const char *const tag,
          const ustring &text);

ustring
b64_encode (const char *buf, const size_t length);

ustring
b64_decode (const ustring &message);

#endif
