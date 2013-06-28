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
#include <sstream>
#include "support/bignum.h"
#include "pki/misc.h"

static ENCODING last_encoding = BASE64;

std::string BN2dec (const BIGNUM * n)
{
   char *tmp = BN_bn2dec (n);
   if (!tmp)
      throw SSL_ERROR;
   std::string return_value (tmp);
   OPENSSL_free (tmp);
   return return_value;
}

std::string BN2b64(const BIGNUM * n) {
   int num_bytes = BN_num_bytes(n);
   VHUtil::array<unsigned char> ain(num_bytes);
   if (0 == BN_bn2bin(n, ain))
      throw SSL_ERROR;
   
   BIO * mem = BIO_new(BIO_s_mem());
   BIO * bio64 = BIO_new(BIO_f_base64());
   if (!mem || !bio64)
      throw SSL_ERROR;

   BIO_set_flags(bio64, BIO_FLAGS_BASE64_NO_NL);
   BIO_push(bio64, mem);
   
   if (BIO_write(bio64, ain, num_bytes) <= 0)
      throw SSL_ERROR;
   if (BIO_flush(bio64) < 1)
      throw SSL_ERROR;
   
   int memsize = BIO_pending(mem);
   VHUtil::array<char> aout(memsize);
   int read = BIO_read(mem, aout, memsize);
   
   if (read <= 0)
      throw SSL_ERROR;
   
   std::string result(aout, memsize);
   BIO_free_all(mem);
   
   return result;
}

namespace {
BIGNUM * b642BN(const std::string & b64,
                const std::string &error_message) {
   BIO * mem = BIO_new (BIO_s_mem ());
   BIO * bio64 = BIO_new(BIO_f_base64());
   if (!mem || !bio64)
      throw SSL_ERROR;

   BIO_set_flags(bio64, BIO_FLAGS_BASE64_NO_NL);
   BIO_push (bio64, mem);
   
   if (BIO_write (mem, b64.data (), b64.size ()) <= 0)
      throw SSL_ERROR;
   if (BIO_flush (mem) < 1)
      throw SSL_ERROR;
   
   VHUtil::array<unsigned char> a(b64.size());
   int inlen = BIO_read(bio64, a, a.m_size);
   if (inlen <= 0)
      VHUtil::_check (("BADLY_FORMED_NUMBER" + error_message).c_str (),
                      __FILE__,
                      __LINE__);

   BIGNUM * result = BN_bin2bn(a, inlen, NULL);
   if (!result)
      throw SSL_ERROR;
   BIO_free_all(mem);
   return result;
}

enum ENCODING
find_encoding_value(const std::string & attr_enc)
{
   enum ENCODING result = USE_LAST;
      
   if      (attr_enc == "BASE64")
      result           = BASE64;
      
   else if (attr_enc == "DEC")
      result           = DEC;
      
   else if (attr_enc == "HEX")
      result           = HEX;
      
   return result;
}
}

BIGNUM *
xml2BN(VHUtil::xml_node n)
{
   BIGNUM * result = 0;
   const std::string data = n->characters();
   std::ostringstream error_message;

   enum ENCODING enc = USE_LAST;
   if (n->has_attribute(ATT_ENCODING))
      enc = find_encoding_value(n->attribute(ATT_ENCODING));

   if (USE_LAST == enc)
   {
      enc = last_encoding;
   }
   else
   {
      last_encoding = ENCODING(enc);
   }
   
   error_message << "BADLY_FORMED_NUMBER: Characters of node `"
                 << n->name ()
                 << "' do not form ";

   if (n->has_attribute(ATT_ENCODING))
   {
      error_message << "a "
                    << n->attribute (ATT_ENCODING)
                    << "-";
   }
   else
   {
      error_message << "an ";
   }

   error_message << "encoded BIGNUM: `"
                 << data
                 << "'";
   
   switch (enc)
   {
   case BASE64:
      result = b642BN(data, error_message.str ());
      break;
   case DEC:
      result = BN_new();
      VH_nonzero (result, SSL_ERROR);
      if (!BN_dec2bn (&result, data.c_str()))
         VHUtil::_check (error_message.str ().c_str (), __FILE__, __LINE__);
      break;
   case HEX:
      result = BN_new();
      VH_nonzero (result, SSL_ERROR);
      if (!BN_hex2bn(&result, data.c_str()))
         VHUtil::_check (error_message.str ().c_str (), __FILE__, __LINE__);;
      break;
   default:
      VH_assert (!"xml2BN: unrecognized encoding");
      break;
   }
   
   return result;
}

VHUtil::xml_node add_BN_element(VHUtil::xml_node n,
                                const std::string & name,
                                const BIGNUM * i,
                                ENCODING enc)
                                
{
   VHUtil::xml_node new_node(n->new_element(name));
   
   add_BN_characters(new_node, i, enc);
   
   n->add_characters("\n");
   return new_node;
}

void
add_BN_characters(VHUtil::xml_node n,
                  const BIGNUM * i,
                  const std::string &alphabet_encoding_xml)
{
   VHUtil::xml_tree alphabet_encoding (alphabet_encoding_xml);
   add_BN_characters (n, i,
      find_encoding_value (alphabet_encoding.root ()->characters ()));
}

void add_BN_characters(VHUtil::xml_node n,
                       const BIGNUM * i,
                       ENCODING enc)

{
   if (USE_LAST == enc)
   {
      enc = last_encoding;
   }

   std::string str_enc;
   switch (enc)
   {
   case BASE64:
      n->add_characters(::BN2b64(i));
      str_enc = "BASE64";
      break;
   case DEC:
      n->add_characters(::BN2dec(i));
      str_enc = "DEC";
      break;
   case HEX: {
      char *free_me = BN_bn2hex(i);
      if (!free_me)
         throw SSL_ERROR;
      n->add_characters(free_me);
      OPENSSL_free (free_me);
      str_enc = "HEX";
   }
      break;
   default:
      VH_assert (!"add_BN_characters: unrecognized encoding");
      break;
   }
   
   n->add_attribute(ATT_ENCODING, str_enc.c_str());
}

BIGNUM * GetHashOf2BNs(const BIGNUM * bn1, const BIGNUM * bn2)
{
   const BIGNUM * both[2];
   both[0] = bn1;
   both[1] = bn2;
   return GetHashOfNBNs (both, sizeof (both) / sizeof (both[0]));
}

BIGNUM * GetHashOfNBNs(const BIGNUM *array[], int n)
{
   BIGNUM * result = 0;
   
   EVP_MD_CTX mdctx;

   unsigned char md_value[EVP_MAX_MD_SIZE];
   unsigned md_len = 0;

   if (0 == EVP_DigestInit(&mdctx, EVP_sha1 ()))
      throw SSL_ERROR;
   
   for (int i=0; i<n; i++)
   {
      int num_bytes_bn = BN_num_bytes(array[i]);
      VHUtil::array<unsigned char> a_bn(num_bytes_bn);
      BN_bn2bin(array[i], a_bn);

      if (0 == EVP_DigestUpdate(&mdctx, a_bn, num_bytes_bn))
         throw SSL_ERROR;
   }
   
   if (0 == EVP_DigestFinal(&mdctx, md_value, &md_len))
      throw SSL_ERROR;
   result = BN_bin2bn(md_value, md_len, NULL);
   if (!result)
      throw SSL_ERROR;

   return result;
}

std::ostream &operator<< (std::ostream & o, BIGNUM * n)
{
   char * as_string = BN_bn2dec(n);
   if (!as_string)
      throw SSL_ERROR;
   o << as_string;
   OPENSSL_free(as_string);
   return o;
}

void
auto_BN::Canonicalize(auto_BN & m)
{
   auto_BN &x = *this;
   
   static auto_BN prev_m;
   static auto_BN minus_m;
   static auto_BN two_m;
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx)
      throw SSL_ERROR;

   // Make a copy of x
   auto_BN x_copy;
   if (!BN_copy(x_copy, x))
      throw SSL_ERROR;
   
   // make a "0" bignum
   auto_BN zero_bn = BN_new();
   if (!zero_bn)
      throw SSL_ERROR;

   if (!BN_zero(zero_bn))
      throw SSL_ERROR;
   
   if (prev_m != m)
   {
      prev_m = m;
      if (!BN_sub(minus_m, zero_bn, m))
         throw SSL_ERROR;
      if (!BN_add(two_m, m, m))
         throw SSL_ERROR;
   }
   
   if ( (zero_bn <= x) && (x < m) )
   {
      // do nothing, x is in the right range
   }
   else if ( (zero_bn <= x) && (x < two_m) )
   {
      if (!BN_sub(x, x_copy, m))
         throw SSL_ERROR;
   }
   else if ( (minus_m <= x) && (x < zero_bn) )
   {
      if (!BN_add(x, x_copy, m))
         throw SSL_ERROR;
   }
   else
   {
      if (!BN_mod(x, x_copy, m, ctx))
         throw SSL_ERROR;
      x_copy = x;
      if (x < zero_bn)
      {
         if (!BN_add(x, x_copy, m))
            throw SSL_ERROR;
      }
   }
   
   return;
}
