#ifndef _FRACTION_H
#define _FRACTION_H
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

/* Fraction handling */
#include <stdbool.h>

struct fraction
{
	unsigned long int numerator;
	/* Never zero */
	unsigned long int denominator;
};

extern const struct fraction fraction_zero, fraction_one;

/* a + b */
extern struct fraction fraction_add(struct fraction a, struct fraction b);

/* (unsigned int)f */
extern unsigned int fraction_truncate(struct fraction f);

/* a > b ? */
extern bool fraction_greater(struct fraction a, struct fraction b);

/* a - b */
extern int fraction_compare(struct fraction a, struct fraction b);

/* a == b ? */
extern bool fraction_equal(struct fraction a, struct fraction b);
#endif /*_FRACTION_H*/
