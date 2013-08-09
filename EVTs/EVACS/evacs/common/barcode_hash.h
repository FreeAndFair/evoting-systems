#ifndef _BARCODE_HASH_H
#define _BARCODE_HASH_H
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

/* This routine not required by client. */
/* Generate bitstring of hash from the barcode data */
#include <limits.h>
#include <unistd.h>
#include <openssl/sha.h>

/* Number of bits in the barcode hash */
#define HASH_BITS 160

extern void gen_hash(char hash[HASH_BITS + 1],
		     const unsigned char barcode_data[],
		     size_t size);
#endif /*_BARCODE_HASH_H*/
