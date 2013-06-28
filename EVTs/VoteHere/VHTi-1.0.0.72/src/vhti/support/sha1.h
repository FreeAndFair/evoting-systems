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
#ifndef SHA1_H_
#define SHA1_H_

#ifndef NULL
#define NULL ((void *) 0)
#endif


#define SHA1DIGSZ  (20)

typedef struct {
  unsigned long state[5];
  unsigned long count[2];
  unsigned char buffer[64];
} SHA1_CTX;

void SHA1Init(
  SHA1_CTX* context
  );
void SHA1Update(
  SHA1_CTX* context,
  const unsigned char* data,
  unsigned int len
  );
void SHA1Final(
  unsigned char digest[SHA1DIGSZ],
  SHA1_CTX* context
  );
void SHA1Transform(
  unsigned long state[5],
  const unsigned char buffer[64]
  );

#endif /* SHA1_H_ */

