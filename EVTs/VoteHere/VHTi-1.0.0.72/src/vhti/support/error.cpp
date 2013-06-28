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
#include <misc/vh_excpt.h>
#include "support/platform.h"

#include <map>
#include <string>

namespace {
   
   class error_container 
   {
   public:
      error_container(void) : m_errno(0) {}
      error_container(int e,
         const std::string & m) : m_errno(e) { m_message = m; }
      
      int m_errno;
      std::string m_message;
   };
   
   typedef std::map<VHTI::thread_type, error_container> last_error_map;
   
   last_error_map g_error_map;
   
};

std::string 
internal_get_last_error(void)
{
   std::string result;

   try {
      result = g_error_map[VHTI::get_current_thread()].m_message.c_str();
      g_error_map.erase(VHTI::get_current_thread());
   } catch (const std::exception & e) {
      result = e.what();
   }
   return result;
}

EXPORT_SYMBOL int 
VHTI_get_last_error(const char ** error_text)
{
   * error_text = NULL;
   int result = -1;
   
   try {
      if (g_error_map.size()) {
         * error_text =
            VHTI_dup(g_error_map[VHTI::get_current_thread()].m_message.c_str());
         g_error_map.erase(VHTI::get_current_thread());
         result = 0;
      }
      
   } catch (const std::exception & e) {
      // Oh, this must be really bad.  Report it as an error and return.
      if (error_text) {
         VHTI_free(* error_text);
      }
      * error_text = VHTI_dup(e.what());
      result = -1;
   }
   return result;
}


EXPORT_SYMBOL int 
VHTI_get_last_error_number(void)
{
   return g_error_map[VHTI::get_current_thread()].m_errno;
}


EXPORT_SYMBOL int
VHTI_set_last_error(const VHUtil::Exception & e)
{
   int result = 0;
   
   try {
      error_container ec(e.getResultNo(), e.what());
      
      g_error_map[VHTI::get_current_thread()] = ec;
   }
   catch (const VHUtil::Exception &) {
      result = -1;
   }
   
   return result;
}
