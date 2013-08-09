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
#include <limits.h>
#include "fraction.h"

const struct fraction fraction_zero = { .numerator = 0, .denominator = 1 };
const struct fraction fraction_one = { .numerator = 1, .denominator = 1 };

/* Find the Greatest Common Divisor: thanks Euclid! */
static long unsigned int gcd(unsigned long int a, unsigned long int b)
{
	if (a == b) return a;
	if (a > b) return gcd(a-b, b);
	else return gcd(a, b-a);
}

/* Reduce to simplest form */
static void normalize(struct fraction *f)
{
	unsigned long int common_divisor;

	/* Avoid potential gcd loop */
	if (f->numerator == 0) return;

	/* Find GCD. */
	common_divisor = gcd((unsigned long int) f->numerator,
			     (unsigned long int) f->denominator);
	f->numerator /= common_divisor;
	f->denominator /= common_divisor;
}

static void same_denominator(struct fraction *a, struct fraction *b)
{
	unsigned long int common_divisor, a_multiplier, b_multiplier;

/* Find GCD. */
	common_divisor = gcd( a->denominator,
			      b->denominator);

	a_multiplier = b->denominator/common_divisor;
	b_multiplier = a->denominator/common_divisor;
	a->denominator *= a_multiplier ; 
	a->numerator *=  a_multiplier ;
	b->denominator *= b_multiplier;
	b->numerator *= b_multiplier;

	/* Multiply out */
	/*a->denominator *= b->denominator;
	a->numerator *= b->denominator;
	b->denominator *= old_a.denominator;
	b->numerator *= old_a.denominator; */

}

/* a + b */
struct fraction fraction_add(struct fraction a, struct fraction b)
{
	struct fraction ret;
	if (a.denominator !=  b.denominator) {
	  same_denominator(&a, &b);
	}
	ret.denominator = a.denominator;
	ret.numerator = a.numerator + b.numerator;
	normalize(&ret);

	return ret;
}

/* (unsigned int)f */
unsigned int fraction_truncate(struct fraction f)
{
	return f.numerator / f.denominator;
}

/* a > b ? */
bool fraction_greater(struct fraction a, struct fraction b)
{
	/* Convert to same denominator */	
	same_denominator(&a, &b);
	return (a.numerator > b.numerator);
}

/* a - b */
int fraction_compare(struct fraction a, struct fraction b)
{
	/* Convert to same denominator */	
	same_denominator(&a, &b);
	if (a.numerator > b.numerator) return 1;
	else if (a.numerator < b.numerator) return -1;
	return 0;
}

/* a == b ? */
bool fraction_equal(struct fraction a, struct fraction b)
{
	/* Convert to same denominator */	
	same_denominator(&a, &b);
	return (a.numerator == b.numerator);
}
