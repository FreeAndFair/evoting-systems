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
// Include the source code directly, so that we can access the
// internal functions.
#include <support/support.cpp>
extern "C" {
#include <misc/cutest.h>
}
#include "support_test.h"
#include <iostream>

const size_t silly_size = 22;
const char silly_string[] = "You talkin' to me?";

void
memory_test (CuTest *tc)
{
   // ensure the global map is empty.

   CuAssert(tc, "global allocation map isn't initially empty", 0 == g_allocation_sizes.size());

   // allocate one chunk; ensure the map contains one entry, with
   // that chunk's address and size.
   char *chunk = VHTI_alloc(silly_size);

   CuAssert(tc, "VHTI_alloc unexpectedly returned 0", 0 != chunk);
   CuAssert(tc, "global allocation map doesn't contain exactly one entry", 1 == g_allocation_sizes.size());
   CuAssert(tc, "global allocation map doesn't contain expected value", silly_size == g_allocation_sizes[chunk]);
   
   // delete that chunk; again ensure the map is empty.
   VHTI_free(chunk); chunk = 0;

   CuAssert(tc, "global allocation map isn't empty after deletion", 0 == g_allocation_sizes.size());

   // do two allocations of the same size; ensure the map contains
   // both entries.
   char *second_chunk = VHTI_alloc(silly_size);
   chunk = VHTI_alloc(silly_size);

   CuAssert(tc, "VHTI_alloc unexpectedly returned 0",(0 != chunk) &&(0 != second_chunk));
   CuAssert(tc, "global allocation map doesn't contain exactly two entries", 2 == g_allocation_sizes.size());
   CuAssert(tc, "global allocation map doesn't contain expected value",(silly_size == g_allocation_sizes[chunk])
            &&(silly_size == g_allocation_sizes[second_chunk]));
   
   // delete one chunk; ensure one entry ...
   VHTI_free(chunk); chunk = 0;
   CuAssert(tc, "global allocation map doesn't contain exactly one entry after deletion", 1 == g_allocation_sizes.size());

   // TODO -- think of a way to check that VHTI_free_without_clearing
   // indeed doesn't clear the memory, and that VHTI_free indeed
   // does.

   VHTI_free_without_clearing(second_chunk); second_chunk = 0;
   CuAssert(tc, "global allocation map isn't empty after deletion", 0 == g_allocation_sizes.size());

   chunk = VHTI_dup(silly_string);
   CuAssert(tc, "VHTI_dup didn't modify the global allocation map", 1 == g_allocation_sizes.size());
   CuAssert(tc, "VHTI_dup isn't duplicating its argument", 0 == strcmp(chunk, silly_string));

   // do lots of allocations, and don't even bother saving the
   // returned pointers.
   VHTI_dup(silly_string);
   VHTI_alloc(10);
   VHTI_alloc(20);
   VHTI_alloc(10000);
   VHTI_alloc(20000);

   CuAssert(tc, "unexpected size of global allocation map", 6 == g_allocation_sizes.size());

   VHTI_free_all();
   CuAssert(tc, "global allocation map isn't empty after VHTI_free_all", 0 == g_allocation_sizes.size());
}
