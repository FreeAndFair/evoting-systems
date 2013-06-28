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

#pragma warning(disable: 4786)
#ifndef BIGNUM_H
#define BIGNUM_H

#include <stdio.h>
#include <fstream>

#include "vhti/support.h"
#include "platform.h"

#include <misc/array.h>
#include <misc/xml_tree.h>
#include <misc/vh_cout.h>
#include <misc/vh_excpt.h>
#include <misc/format_string.h>

#include <openssl/bn.h>
#include <openssl/bio.h>
#include <openssl/dsa.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>

#include <support/auto_c_ptr.h>

#ifdef __cplusplus

namespace VHInternal {
   // If you change one of these, you must change the other!
   const char digest_name[] = "SHA1";
   const unsigned short digest_bits = 160;
}

// The USE_LAST encoding ensures that whatever encoding
// you received last is the form
// that you will send next.
enum ENCODING {
   USE_LAST,
      BASE64,
      DEC,
      HEX
};

std::string
BN2dec (const BIGNUM * n);

std::string
BN2b64(const BIGNUM * n);

VHUtil::xml_node
add_BN_element(VHUtil::xml_node n, const std::string & name,
               const BIGNUM * i, ENCODING enc = USE_LAST);

void
add_BN_characters(VHUtil::xml_node n, const BIGNUM * i, ENCODING enc = USE_LAST);

void
add_BN_characters(VHUtil::xml_node n, const BIGNUM * i, const std::string &enc_xml);

BIGNUM *
xml2BN(VHUtil::xml_node n);

BIGNUM *
GetHashOf2BNs(const BIGNUM * bn1, const BIGNUM * bn2);

BIGNUM *
GetHashOfNBNs(const BIGNUM *array[], int n);

class auto_BN
{
public:
   auto_BN(void)
      : m_bn(BN_new())
   {
      VH_nonzero (m_bn, BN_NEW);

      // I'm not sure that this call to BN_zero is necessary, but it
      // feels safer to make the call than not to.
      VH_nonzero (BN_zero (m_bn), BN_ZERO);
   }

   auto_BN(const BIGNUM * bn) 
      : m_bn(BN_dup (bn)) 
   {
      // 0 is a perfectly valid return value from BN_dup -- it
      // represents the number zero.  The OpenSSL docs don't make this
      // clear, but the source (for version 0.9.7b) does
      // (crypto/bin/bn_lib.c).
      VH_nonzero ((!bn || m_bn), BN_DUP);
   }

   auto_BN(const auto_BN & o)
      : m_bn(BN_dup(o.m_bn))
   {
      VH_nonzero ((!o.m_bn || m_bn), BN_dup);
   }
   virtual ~auto_BN(void) 
   { 
      free(); 
   }
   auto_BN & operator = (const auto_BN & o)
   {
      free();
      m_bn = BN_dup(o.m_bn);
      VH_nonzero ((!o.m_bn || m_bn), BN_DUP);
      return * this;
   }
   auto_BN & operator = (const BIGNUM * bn) 
   { 
      free(); 
      m_bn = BN_dup (bn); 
      VH_nonzero ((!bn || m_bn), BN_DUP);
      return * this; 
   }
   bool operator != (const auto_BN & o) const
   {
      return ( (-1 == BN_cmp(this->m_bn, o.m_bn))
         || (1 == BN_cmp(this->m_bn, o.m_bn)) );
   }
   bool operator < (const auto_BN & o) const
   {
      return -1 == BN_cmp(this->m_bn, o.m_bn);
   }
   bool operator <= (const auto_BN & o) const
   {
      return ( (-1 == BN_cmp(this->m_bn, o.m_bn))
         || (0 == BN_cmp(this->m_bn, o.m_bn)) );
   }
   operator BIGNUM * (void) 
   { 
      return m_bn; 
   }
   operator const BIGNUM * (void) const
   { 
      return m_bn; 
   }
   BIGNUM * operator ->(void) const
   {
      return m_bn;
   }
   BIGNUM & operator * (void) const
   {
      return * m_bn;
   }
   virtual void free(void) 
   { 
      if (m_bn) { 
         BN_clear_free(m_bn); 
      } 
      m_bn = NULL;
   }
   void
      Canonicalize(auto_BN & m);
   
private:
   BIGNUM * m_bn;
};

std::ostream &operator<< (std::ostream &, BIGNUM *);

class free_BN_CTX {
public:
   static void free(BN_CTX * ctx)
   {
      BN_CTX_free(ctx);
   }
};
typedef auto_C_PTR<BN_CTX, free_BN_CTX> auto_BN_CTX;

class free_BN_RECP_CTX {
public:
   static void free(BN_RECP_CTX * ctx)
   {
      BN_RECP_CTX_free(ctx);
   }
};
typedef auto_C_PTR<BN_RECP_CTX, free_BN_RECP_CTX> auto_BN_RECP_CTX;

#endif
#endif
