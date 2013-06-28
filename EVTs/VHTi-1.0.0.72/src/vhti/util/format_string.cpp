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

#include <misc/format_string.h>
#include <vhti/support.h>
#include <string>
#include <cassert>
#include <stdarg.h>
#include <stdio.h>

#if defined(_WIN32)

namespace
{
int vasprintf(char** ptr,const char* f, va_list args)
{
   *ptr=0;
   // The buffer size
   int bufSize=1024;
   // A flag to indicate whether the print was successful
   int written=-1;

   while( true )
   {
      *ptr=static_cast<char*>(::VHTI_alloc(bufSize));

      written=::_vsnprintf(*ptr,bufSize,f,args);
      if ( written>=0 )
         break;

      if( written < -1 )
         return NULL;

      ::free(*ptr);
      bufSize*=2;
   }

   return written;
}

}

#elif !defined (__CYGWIN__)

extern "C" int vasprintf __P ((char **__restrict __ptr,
                                 __const char *__restrict __f, _G_va_list __arg))
  __attribute__ ((__format__ (__printf__, 2, 0)));
#endif

std::string VHUtil::format(const char * format, ...)
{
   // A list of arguments
   va_list ap;
   va_start(ap, format);
   // A print buffer
   char * buf;
   vasprintf(& buf, format, ap);
   // The return string made from the buffer
   std::string result(buf);
   free(buf);
   va_end(ap);
   return result;
}

void VHUtil::format(std::string & s, const char * format, ...)
{
   // A list of arguments
   va_list ap;
   va_start(ap, format);
   // A print buffer
   char * buf;
   vasprintf(& buf, format, ap);
   s = buf;
   free(buf);
   va_end(ap);
}

void VHUtil::vformat(std::string & s, const char * format, va_list args)
{
   // A print buffer
   char * buf=0;
   vasprintf(& buf, format, args);
   s = buf;
   ::free(buf);
}

