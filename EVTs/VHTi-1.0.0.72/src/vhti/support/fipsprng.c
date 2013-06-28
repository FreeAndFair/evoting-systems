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
/*
 * PRNG from FIPS-186-2 Appendix 3.1
 * Designed to meet FIPS-140-2 criteria.
 *
 * Copyright 2003, Robert W. Baldwin, all rights reserved.
 * This software may be used for any commercial or non-commercial
 * purpose including creating derivative works, provided that this 
 * copyright notice is included and the user agrees to hold
 * the author harmless for any and all claims resulting from
 * the use of this software.
 */

#include <string.h>
#include <limits.h>
#include "fipsprng.h"

#if ((PRNG_STATESZ < 20) || (64 < PRNG_STATESZ))
The PRNG_STATESZ value must be between 20 and 64 inclusive;
#endif
#if LONG_MAX != ((1UL << 31) - 1)
#error The long type must be four bytes;
#endif
 
int FIPS186Generator (
  unsigned char    XKEY[PRNG_STATESZ],   /* In/Out PRNG secret state */
  const unsigned char    *optionalSeed,  /* Can be NULL if seedLength == 0 */
  unsigned long    seedLength,
  unsigned char    *output,              /* Can be NULL if outputLength == 0 */
  unsigned long    outputLength          /* Set to zero to just mix in seed */
  )
{
  int m = 0, j = 0, k = 0;
  unsigned long fillsize = 0;
  int  sum = 0, carry = 0;
  int status;
  SHA1_CTX digestContext;
  unsigned char XSEED[SHA1DIGSZ] = {'\0'};
  unsigned char XVAL[64] = {'\0'};     /* Input buffer for SHA1Transform */
  unsigned char X[SHA1DIGSZ] = {'\0'};
  unsigned char PrevX[SHA1DIGSZ] = {'\0'};
  unsigned long t[5] = {
                  0xefcdab89,
                  0x98badcfe,
                  0x10325476,
                  0xc3d2e1f0,
                  0x67452301};
  
  if (NULL == XKEY ||
      ((seedLength != 0) && (optionalSeed == NULL)) ||
      ((outputLength != 0) && (output == NULL)))
  {
    return ERROR_PARAMETER;
  }

  /* The FIPS-186 appendix does not specify how XSEED is generated.
   * This construct, which prepends XKEY to the seed bytes, is used
   * to avoid a weakness that RSA Labs found in some seeding algorithms.
   * We want to ensure that if ten small seed values are entered, where
   * each seed is either the “0” or “1” character with 50-50 chance, then
   * the XKEY can end up in 1024 different new states.  Without prepending
   * XKEY inside the SHA1 function, the final value of XKEY would 
   * only depend on the total number of “1” values in the ten input seeds, 
   * not on their order.  Thus there would only be ten possible
   * new states for XKEY.
   *
   * XSEED = SHA1 (XKEY || SeedBytes) or zero if no seed bytes.
   */
  if (seedLength != 0) {
    SHA1Init (&digestContext);
    SHA1Update (&digestContext, XKEY, sizeof(XKEY));
    SHA1Update (&digestContext, optionalSeed, seedLength);
    SHA1Final (XSEED, &digestContext);
  }
  else {
    memset (XSEED, 0, sizeof(XSEED));
  }

  /* 
   * XVAL = XKEY + XSEED
   */
  carry = 0;
  for (k = 0 ; k < sizeof(XSEED) ; k++)
  {
    sum = carry + XKEY[k] + XSEED[k];
    XVAL[k] = sum & 0xFF;
    carry = (sum >> 8) & 0x1;  /* The “& 0x1” won’t be needed if */
                               /* the compile handles unsigned right */
  }
  if (sizeof(XSEED) < sizeof(XKEY)) {
    for (k = sizeof(XSEED) ; k < sizeof(XKEY) ; k++) {
      sum = carry + XKEY[k];
      XVAL[k] = sum & 0xFF;
      carry = (sum >> 8) & 0x1;  /* The "& 0x1" won’t be needed if */
    }
  }

  /* Let m be the number of 20 byte blocks needed to fill output */
  m = (outputLength + (sizeof(X) - 1)) / sizeof(X);
  m = m + 1;   /* Do extra loop to create PrevX */
 
  /* Start of the X generation loop */
  status = ERROR_NONE;
  for (j = 0 ; j < m ; j++ ) {
    /*
     * X = G (t, XVAL)
     *
     * Fill in X with FIPS constant for SHA1Transform input.
     * SHA1Transform puts result in X and modifies XVAL.
     */
    memcpy (X, t, sizeof(t));
    SHA1Transform ((unsigned long *)X, XVAL);

    /*
     * XKEY = 1 + XKEY + X
     *
     * When X equals minus one and PRNG_STATESZ == SHA1DIGSZ,
     * then XKEY will not change.  This happens so rarely,
     * that we don't check for it.  We let the continuous
     * random number test (PrevX == X), which is required
     * by the FIPS-140 criteria, notice the problem and
     * raise an alarm.  The caller can fix the problem
     * by adding any seed that produces a non-zero XSEED.
     * This was not needed in FIPS-186 because the mod q
     * step ensured that X could not be “minus one”, so
     * XKEY was guaranteed to change.
     */
    carry = 1;
    for (k = 0 ; k < sizeof(X) ; k++)
    {
      sum = carry + XKEY[k] + X[k];
      XKEY[k] = sum & 0xFF;
      carry = (sum >> 8) & 0x1;
    }
    if (sizeof(X) < sizeof(XKEY)) {
      for (k = sizeof(X) ; k < sizeof(XKEY) ; k++) {
        sum = carry + XKEY[k];
        XKEY[k] = sum & 0xFF;
        carry = (sum >> 8) & 0x1;
      }
    }

    /* Infogard labs says we should only use XSEED once.
     * XVAL = XKEY + zero   
     */
    memcpy (XVAL, XKEY, sizeof(XKEY));
    /* SHA1Transform modifies both args, so we must zero remaining bytes */
    memset (XVAL + sizeof(XKEY), 0, sizeof(XVAL) - sizeof(XKEY));

    /*
     * Return alarm error if PrevX == X
     * Otherwise set PrevX = X
     * First time through, just set PrevX.
     * Make sure code runs in constant time.
     */
    if (j > 0) {
      sum = 0;
      for (k = 0 ; k < sizeof(X) ; k++)
      {
        sum += (X[k] != PrevX[k]) ? 1 : 0;
      }
      if (sum == 0)
      {
        status = ERROR_ALARM;
        break;
      }
      /* Fill in output with up to 20 bytes */
      fillsize = (outputLength >= sizeof(X)) ? sizeof(X) : outputLength;
      memmove (output, X , fillsize);
      output += fillsize;
      outputLength -= fillsize;
    }
    memcpy (PrevX, X, sizeof(X));
  } /* End of the X generation loop. */

  /* Zeroize all temporary variables */
  /* Make sure optimizer does not remove these operations. */
  memset (XSEED, 0, sizeof(XSEED));
  memset (XVAL, 0, sizeof(XVAL));
  memset (X, 0, sizeof(X));
  memset (PrevX, 0, sizeof(PrevX));
  memset (t, 0, sizeof(t));
  memset (&digestContext, 0, sizeof(digestContext));
  return status;
}
