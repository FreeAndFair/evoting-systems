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

#include "vhti/types.h"
#include "support_test/test-data.h"

// These are all well-formed, but invalid.
const char *const invalid_random_state = "<" VOTER_ROLL " />";
const char *const invalid_random_ij_state = "<" VOTER_ROLL " />";

const char *const valid_random_state =
"<RandomState SourceType=\"PSEUDO FROM HASH\">"
"<RandomSeedKey>"
"Some kind of random data to hash"
"</RandomSeedKey>"
"<RandomBlock Encoding=\"DEC\">"
"1080159859926833460887638203863366617559462040602"
"</RandomBlock>"
"</RandomState>";

const char *const valid_random_ij_state =
"<RandomIJState SourceType=\"PSEUDO FROM HASH\">"
"<RandomSeedKey>"
"Some kind of random data to hash"
"</RandomSeedKey>"
"</RandomIJState>";
