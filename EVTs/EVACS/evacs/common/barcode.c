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
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include "barcode.h"

/* This is the encoding mapping we use */
static const char enc_string[(1 << BARCODE_BITS_PER_SYM) + 1]
= "abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ23456789-+*/$%&";

/* Put up to len bits from v into the 6 bit character array starting
   at the given bit offset. */
static void put_bits(unsigned char *output,
		     uint32_t v,
		     unsigned int offset,
		     unsigned int len)
{
	unsigned int i;

	/* Sanity check: < 32 bits, and any other bits will be zero. */
	assert(len < 32);
	assert((v & ~((((uint32_t)1)<<len)-1)) == 0);

	for (i=0; i < len; i++) {
		/* Find location in the output. */
		int bit  = (offset+i) % BARCODE_BITS_PER_SYM;
		int byte = (offset+i) / BARCODE_BITS_PER_SYM;

		/* If this bit is set in the value, set it in the output */
		if ((v & (1U<<i)) != 0)
			output[byte] |= (1<<bit);
		else
			output[byte] &= ~(1<<bit);
	}
}

void bar_encode_ascii(struct barcode *bc)
{
	int i;
	unsigned char code[BARCODE_ASCII_BYTES];

	/* Do one byte at a time conversion */
	memset(code, 0, sizeof(code));
	for (i = 0; i < sizeof(bc->data); i++)
		put_bits(code, bc->data[i], i*CHAR_BIT, CHAR_BIT);

	/* Append checksum */
	put_bits(code, bc->checksum, i*CHAR_BIT, BARCODE_CHECKSUM_BITS);

	/* Map each one to a character */
	for (i=0; i < BARCODE_ASCII_BYTES; i++) {
		assert(code[i] < strlen(enc_string));
		bc->ascii[i] = enc_string[code[i]];
	}
	/* nul terminate */
	bc->ascii[i] = '\0';
}

static bool decode_symbol(char c, unsigned char *code)
{
	const char *p;

	p = strchr(enc_string, c);
	if (!p) return false;
	*code = (unsigned char)(p - enc_string);
	return true;
}

/* pull bits from a 6 bit character array into a uint32_t */
static uint32_t pull_bits(unsigned char *code, unsigned *offset, unsigned len)
{
	unsigned i;
	uint32_t v = 0;

	for (i=0; i<len; i++) {
		int bit  = ((*offset)+i) % BARCODE_BITS_PER_SYM;
		int byte = ((*offset)+i) / BARCODE_BITS_PER_SYM;
		if (code[byte] & (1<<bit)) v |= (((uint32_t)1)<<i);
	}

	(*offset) += len;

	return v;
}

bool bar_decode_ascii(struct barcode *bc)
{
	unsigned char code[BARCODE_ASCII_BYTES];
	int i;
	/* SIPL 2011: Changed type of bit to conform to parameter type. */
	unsigned int bit=0;

	for (i=0; i < BARCODE_ASCII_BYTES; i++)
		if (!decode_symbol(bc->ascii[i], &code[i])) {
			fprintf(stderr, "Decoding `%s' digit %u failed\n",
				bc->ascii, i);
			return false;
		}

	for (i=0; i < sizeof(bc->data); i++)
		bc->data[i] = pull_bits(code, &bit, CHAR_BIT);
	bc->checksum = pull_bits(code, &bit, BARCODE_CHECKSUM_BITS);
	return true;
}

/* DDS3.2.1: Generate Checksum */
unsigned int gen_csum(const struct barcode *bc)
{
	unsigned int i, sum;

	sum = 0;
	for (i = 0; i < sizeof(bc->data); i++)
		sum += bc->data[i];

	return sum % 16;
}
