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

#include "vhti/support.h"
#include "mutex.h"
#include "support_internal.h"
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <map>
#include <util/validate.h>
#include <misc/vh_cout.h>
#include <misc/xml_tree.h>
#include <vhti/support.h>
#include <vhti/types.h>
#include "platform.h"

#include <string.h>
#include <stdlib.h>


namespace {
   const char g_default_dtd [] =
#include "./default-dtd.h"
   ;
   std::string g_dtd;
};

namespace {
   std::map<const char *, size_t> g_allocation_sizes;
};

EXPORT_SYMBOL char *
VHTI_alloc(size_t num_bytes)
{
   char *return_value = static_cast<char *>(::malloc(num_bytes));
   if (return_value)
   {
      VHUtil::AutoMutex am(VHInternal::g_mutex);
      g_allocation_sizes[return_value] = num_bytes;
   }
   return return_value;
}

namespace {
   // This function does not protect g_allocation_sizes with the
   // mutex; its callers must do that.
   void
   internal_free_iterator(std::map<const char *, size_t>::iterator it,
                          const bool fClear)
   {
      VH_zero(g_allocation_sizes.end() == it,
              FREEING_BAD_POINTER);

      if (fClear)
      {
         ::memset(static_cast<void *>(const_cast<char *>(it->first)), '\0', it->second);
      }
      ::free (static_cast<void *>(const_cast<char *>(it->first)));
   }

   // This function *does* protect g_allocation_sizes with the mutex.
   void
   internal_free_ptr(const char *thing,
                     const bool fClear)
   {
      if (thing) 
      {
         VHUtil::AutoMutex am(VHInternal::g_mutex);
         std::map<const char *, size_t>::iterator it(g_allocation_sizes.find(thing));
         internal_free_iterator(it, fClear);
         g_allocation_sizes.erase(it);
      }
   }
};

EXPORT_SYMBOL int
VHTI_free (const char *thing)
{
   internal_free_ptr(thing, true);
   return 0;
}

EXPORT_SYMBOL int
VHTI_free_all()
{
   VHUtil::AutoMutex am(VHInternal::g_mutex);

   for (std::map<const char *, size_t>::iterator i = g_allocation_sizes.begin();
        i != g_allocation_sizes.end();
        i++)
   {
      internal_free_iterator(i, true);
   }

   g_allocation_sizes.erase (g_allocation_sizes.begin(),
                             g_allocation_sizes.end());

   return 0;
}

EXPORT_SYMBOL int
VHTI_free_without_clearing (const char *thing)
{
   internal_free_ptr(thing, false);
   return 0;
}

EXPORT_SYMBOL char * 
VHTI_dup (const char * thing)
{
   size_t len = 1 + strlen(thing);  // gotta remember the null termination.
   char * result = VHTI_alloc(len);
   if (result) 
   {
      ::strncpy(result, thing, len);
   }
   return result;
}

int
VHTI_set_DTD_location (const char *path)
{
   int status = 0;

   std::ostringstream dtd_stringstream;
   std::auto_ptr<std::ifstream> dtd (new std::ifstream(path));

   if (dtd->fail ())
   {
      std::cerr << "Couldn't open "
                << path
                << ": "
                << strerror (errno)
                << std::endl;
      status = errno;
   }
   else
   {
      std::string tmp;
      while (std::getline (*dtd, tmp))
      {
         dtd_stringstream << tmp << std::endl;
      }
   }

   g_dtd = dtd_stringstream.str ();

   return status;
}

// The following functions return 0 for SUCCESS and non-zero for FAILURE

// 0 means "valid".
int
VHTI_validate (const char * datatype, const char * data)
{
   int return_value = 1;

   if (0 == g_dtd.size ())
   {
      g_dtd = g_default_dtd;
   }
   
   VHUtil::xml_tree xmlt (data, VHUtil::xml_tree::NO_THROW);
      
   if (!xmlt.parsed_OK ())
   {
      VHUtil::cout () << "`"
                      << data
                      << "' isn't well-formed XML"
                      << std::endl;
   }
   else if (xmlt.root ()->name () != datatype)
   {
      VHUtil::cout () << "Expected root element `"
                      << datatype
                      << "'; instead got `"
                      << xmlt.root ()->name ()
                      << "'"
                      << std::endl;
   }
   else if (!VHUtil::validate_xml_document (data,
                                            g_dtd,
                                            false))
   {
      VHUtil::cout () << "`"
                      << data
                      << "' doesn't validate against the dtd "
                      << std::endl;
   }
   else
   {
      return_value = 0;
   }

   return return_value;
}
