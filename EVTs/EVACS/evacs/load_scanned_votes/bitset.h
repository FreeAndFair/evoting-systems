#ifndef _BITSET_H
#define _BITSET_H

/* This file is (C) copyright 2008 Software Improvements, Pty Ltd */

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

/* Utilities for bit arrays */

/* Provides CHAR_BIT (= 8) */
#include <limits.h>

/* Define your bitset as an array of these */
#define BITSET_UNIT unsigned long

/* The number of bits in each element of your array */
#define BITSET_UNIT_SIZE (sizeof(BITSET_UNIT) * CHAR_BIT)

/* Assumes BITSET_UNIT_SIZE is a power of two. */
#define BITSET_LENGTH_IN_UNITS(length) \
  ((((length) + BITSET_UNIT_SIZE - 1) & ~(BITSET_UNIT_SIZE - 1)) \
    / BITSET_UNIT_SIZE)

#define BITSET_SMALL_KEY_TO_MASK(bit) (1UL << (bit))
#define BITSET_KEY_TO_POSITION(bit) ((bit) / BITSET_UNIT_SIZE)
#define BITSET_KEY_TO_SMALL_KEY(bit) ((bit) % BITSET_UNIT_SIZE)
#define BITSET_IS_SET(array,bit) \
  ( \
  ((array)[BITSET_KEY_TO_POSITION(bit)]) & \
  BITSET_SMALL_KEY_TO_MASK(BITSET_KEY_TO_SMALL_KEY(bit)) \
  )
#define BITSET_SET_BIT(array,bit) \
  ( \
  ((array)[BITSET_KEY_TO_POSITION(bit)]) |= \
  BITSET_SMALL_KEY_TO_MASK(BITSET_KEY_TO_SMALL_KEY(bit)) \
  )

/* Need to include <string.h> to get memset. */
#define BITSET_CLEAR(array) memset((array),0,sizeof(array))


#endif /* _BITSET_H */
