#ifndef _DISPLAY_FIRST_PREFERENCES_H
#define _DISPLAY_FIRST_PREFERENCES_H
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
#include <common/evacs.h>
#include <counting/fraction.h>
#include <counting/hare_clark.h>

/* SIPL 2011-08-19 Now support counting only pre-poll or only
   polling-day votes. Pass in one of the following integer values
   as the second command-line parameter. If the following are modified
   or added to, modify pp_start.sh to match. */

#define PRE_POLL 0
#define POLLING_DAY 1

/* String representations of the above constants. */
extern const char * const qualification_names[];

#endif /*_DISPLAY_FIRST_PREFERENCES_H*/
