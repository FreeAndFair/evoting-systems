#ifndef _BARCODE_H
#define _BARCODE_H
/* This file is (C) copyright 2001 Software Improvements, Pty Ltd */

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

/* Barcode definitions */
#include <limits.h>
#include <unistd.h>
#include <stdbool.h>

/* Number of bits in a barcode (without checksum) */
#define BARCODE_DATA_BITS 128

/* Number of checksum bits */
#define BARCODE_CHECKSUM_BITS 4

/* Total number of bits */
#define BARCODE_BITS (BARCODE_DATA_BITS + BARCODE_CHECKSUM_BITS)

/* How many bytes things fit into (rounded up) */
#define BYTES(bits) (((bits) + CHAR_BIT-1) / CHAR_BIT)

/* Number of bits per symbol in ascii representation */
#define BARCODE_BITS_PER_SYM 6

/* How many characters that is when represented in ASCII */
#define BARCODE_ASCII_BYTES						 \
	((BARCODE_BITS + BARCODE_BITS_PER_SYM-1) / BARCODE_BITS_PER_SYM)

/* Everything you could ever want to know about a barcode */
struct barcode
{
	/* The random number */
	unsigned char data[BYTES(BARCODE_DATA_BITS)];

	/* The checksum */
	unsigned char checksum;

	/* nul-terminated ASCII barcode representation */
	char ascii[BARCODE_ASCII_BYTES+1];
};

/* Set ascii encoding from checksum and data */
extern void bar_encode_ascii(struct barcode *bc);

/* Set checksum and data from ascii encoding */
extern bool bar_decode_ascii(struct barcode *bc);

/* Generate checksum from the barcode data */
extern unsigned int gen_csum(const struct barcode *bc);

#endif /*_BARCODE_H*/
