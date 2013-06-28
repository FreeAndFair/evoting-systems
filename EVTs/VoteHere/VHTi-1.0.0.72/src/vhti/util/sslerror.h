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
#ifndef SSLERROR_H
#define SSLERROR_H

#include <string>
#include <sstream>
#include <openssl/err.h>
#include "misc/vh_excpt.h"

namespace VHUtil {
   // turn the accumulated SSL errors into a string
   inline
   std::string
      ssl_errors ()
      {
         ERR_load_crypto_strings ();

         std::ostringstream errors;
         unsigned long error = ERR_get_error ();

         while (error)
         {
            char buf [120]; // max required size according to ERR_error_string(3ssl)
            errors << ERR_error_string (error, buf)
                   << std::endl;
            error = ERR_get_error ();
         }

         ERR_free_strings ();
         return errors.str ();
      }
}

#define SSL_ERROR       VHUtil::Exception (__FILE__, __LINE__, VHUtil::ssl_errors ().c_str ())

#endif
