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
#ifndef FIPSPRNG_H_
#define FIPSPRNG_H_
/*
 * PRNG from FIPS-186-2 Appendix 3.1 using G from SHA1.
 * Designed to meet FIPS-140-2 criteria.
 *
 * Copyright 2003, Robert W. Baldwin, all rights reserved.
 * This software may be used for any commercial or non-commercial
 * purpose including creating derivative works, provided that this 
 * copyright notice is included and the user agrees to hold
 * the author harmless for any and all claims resulting from
 * the use of this software.
 */

#include "sha1.h"

#define ERROR_NONE      (0)
#define ERROR_PARAMETER (1)
#define ERROR_ALARM     (2)

/* The state can be between 20 and 64 bytes. */
#define PRNG_STATESZ    (32)

/*
 * This routine provides both mixing of seed bytes
 * and generation of pseudo-random output bytes.
 * It updates a state array (XKEY) after each call.
 * It is designed to meet FIPS-140-2 requirements including
 * a continuous random number test and the use of a
 * FIPS approved PRNG algorithm (FIPS-186 Appendix 3.1 based
 * on the SHA1 G transform).
 *
 * To just add seed bytes, set output = NULL and outoutLength = 0.
 * To just generate output, set optionalSeed = NULL and seedLength = 0.
 * It is possible to do both in a single call, in which case the
 * seed bytes are mixed into the XKEY before output is generated.
 *
 * XKEY must be kept secret from attackers.
 */
int FIPS186Generator (
  unsigned char    XKEY[PRNG_STATESZ],   /* In/Out secret PRNG state */
  const unsigned char    *optionalSeed,  /* Can be NULL if seedLength == 0 */
  unsigned long    seedLength,           /* Length in bytes. */
  unsigned char    *output,              /* Can be NULL if outputLength == 0 */
  unsigned long    outputLength          /* Set to zero to just mix in seed */
  );

#endif /* FIPSPRNG_H_ */
