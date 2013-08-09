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

/* this file contains the accessors for ballot contents   */
#include <stdlib.h>
#include <assert.h>
#include "ballot_contents.h"
#include "evacs.h"


static struct ballot_contents *ballot_contents = NULL;

/* DDS???: Get Ballot Contents */
struct ballot_contents *get_ballot_contents(void)
{
	return ballot_contents;
}

/* Set the ballot contents (called from authenticate) */
void set_ballot_contents(struct ballot_contents *bc)
{
	ballot_contents = bc;
}



