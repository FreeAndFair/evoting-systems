/* This file is (C) copyright 2001 Software Improvements, Pty Ltd.
   Based on prototypes/codegen/evacs_barcode.c and
   prototypes/codegen/encode.c:
	   Copyright (C) Andrew Tridgell 2001
	   Copyright (C) David Gibson 2001 */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */
#include <assert.h>
#include "barcode_hash.h"

/* DDSv1A-3.2.1: Generate Hash */
/* Hash generated is a bitstring: ie. "010101010111" */
void gen_hash(char hash[HASH_BITS + 1],
	      const unsigned char barcode_data[],
	      size_t size)
{
	unsigned char sha_md[SHA_DIGEST_LENGTH];
	char *hashp = hash;
	unsigned int i,b;

	assert(HASH_BITS == SHA_DIGEST_LENGTH*CHAR_BIT);

	/* Call the library routine to do it in one fell swoop */
	SHA1(barcode_data, size, sha_md);

	/* Convert to bitstring, eg. 0xfeed to 1111111011101101. */
	for (i = 0; i < SHA_DIGEST_LENGTH; i++) {
		for (b = 0; b < CHAR_BIT; b++) {
			if ((sha_md[i] >> b) & 1)
				*hashp = '1';
			else
				*hashp = '0';
			hashp++;
		}
	}
	assert(hashp == hash + HASH_BITS);

	/* nul-terminate the string */ 
	*hashp = '\0';
}
