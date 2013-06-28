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

#ifndef SUPPORT_H
#define SUPPORT_H

#include "vhti/types.h"
#include "vhti/export.h"
#include "vhti/error.h"
#include <stdlib.h>              /* for size_t */

#if defined(_MSC_VER)
// 4786: identifer was truncated in debug information
#pragma warning(disable: 4786)
#endif

#ifdef __cplusplus

template <class kind> 
class auto_freeing 
{
public:
   auto_freeing(kind p = 0) : m_p(p) { }
   ~auto_freeing(void) { VHTI_free(m_p); }
   operator char * (void) { return (char *)m_p; }
   operator const kind (void) const { return m_p; }
   kind * operator & (void)
      { 
         if (m_p)
         {
            VHTI_free (m_p);
            m_p = 0;
         }
         return & m_p;
      }
   void operator = (char * p)
      {
         if (m_p)
            VHTI_free (m_p);

         m_p = p;
      }
private:
   kind m_p;
};
#endif

#ifdef __cplusplus
extern "C"
{
#endif

// Public API

// For all return values, 0 is success; anything else is an error code
// which I haven't bothered defining.

// All `out' `char *' parameters must be freed with one of the
// `VHTI_free' functions.

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
EXPORT_SYMBOL char *
VHTI_alloc(size_t num_bytes);

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
EXPORT_SYMBOL int
VHTI_free (const char *thing);

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
// As above, but does not zero the freed block.
EXPORT_SYMBOL int
VHTI_free_without_clearing (const char *thing);

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
EXPORT_SYMBOL char *
VHTI_dup (const char *thing);

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
// Frees all allocations that haven't already been freed with
// `VHTI_free'.
EXPORT_SYMBOL int
VHTI_free_all();

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
// You'd expect this function to be declared in types.h, since it is
// defined in types.cpp.  However, the perl code that automatically
// generates the perl wrapper makes a point of not reading types.h.
// Therefore we declare it here.
EXPORT_SYMBOL int
VHTI_set_DTD_location (const char *path);

/* This function does not follow the normal VHTI conventions, and its 
 * documentation is not auto-generated.  If you change this prototype,
 * please also change the corresponding LaTeX documentation. */
/* 0 means "valid" */
EXPORT_SYMBOL int
VHTI_validate (const char * datatype, const char * data);


#ifdef __cplusplus
}
#endif
#endif
