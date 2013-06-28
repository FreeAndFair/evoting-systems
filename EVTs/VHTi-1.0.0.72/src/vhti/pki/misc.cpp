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

#include <string>
#include <sstream>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <vhti/support.h>
#include <misc/vh_excpt.h>
#include <misc/xml_tree.h>

#include "misc.h"

ustring
xml_wrap (const char *const tag,
          const ustring &text)
{
   std::string complete_tag = "<";
   complete_tag += tag;
   complete_tag += "/>";
   VHUtil::xml_tree xt (complete_tag);
   xt.root ()->add_characters ((const char *)text.c_str ());
   std::ostringstream tmp;
   tmp << *(xt.root ());
   return (unsigned char *) tmp.str ().c_str ();
}

ustring
b64_encode (const char *buf, const size_t length)
{
   bool succeeded = false;
   ustring rv;

   auto_BIO mem    (BIO_new (BIO_s_mem ()));
   auto_BIO filter (BIO_new (BIO_f_base64()));

   if (!mem || !filter)
      throw SSL_ERROR;
   
   BIO_set_flags(((BIO *) filter), BIO_FLAGS_BASE64_NO_NL);
   BIO_push  (filter, mem);

   if ((BIO_write (filter, buf, length) >= 0)
       &&
       (1 == BIO_flush (filter)))
   {
      const int to_read = BIO_pending (mem);
      unsigned char *tmp_buf = (unsigned char *) VHTI_alloc (to_read + 1);
      if (BIO_read(mem, tmp_buf, to_read) >= 0)
      {
         tmp_buf[to_read] = '\0';
         rv.assign (tmp_buf);
         succeeded = true;
      }
      free (tmp_buf);
   }

   if (!succeeded)
      throw SSL_ERROR;

   return rv;
}

ustring
b64_decode (const ustring &message)
{
   bool succeeded = false;
   auto_BIO mem    (BIO_new (BIO_s_mem ()));
   auto_BIO filter (BIO_new (BIO_f_base64()));
   ustring rv;

   BIO_set_flags(((BIO *) filter), BIO_FLAGS_BASE64_NO_NL);
   BIO_push  (filter, mem);

   if ((BIO_write (mem,
                   message.data (),
                   message.size ()) >= 0)
       &&
       (1 == BIO_flush (mem)))
   {
      const unsigned int Length = BIO_pending (filter);
      {
         unsigned char *tmp_buf = (unsigned char *) VHTI_alloc (Length);
         const int nread = BIO_read(filter, tmp_buf, Length);
         if (nread >= 0)
         {
            succeeded = true;
            rv.assign (tmp_buf, nread);
         }
         free (tmp_buf);
      }
   }

   if (!succeeded)
      throw SSL_ERROR;

   return rv;
}
