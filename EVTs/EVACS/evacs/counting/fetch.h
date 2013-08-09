#ifndef _FETCH_H
#define _FETCH_H
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

/* Database interface routines for counting. */
#include <common/database.h>
#include "hare_clark.h"

/* number of digits in the preference_list field for one preference */
#define DIGITS_PER_PREF 6

/* Case-insensitive search for electorate: NULL if not found. */
extern struct electorate *fetch_electorate(PGconn *conn, const char *ename);

/* Given the non-NULL electorate, fill in all the groups, return number. */
extern unsigned int fetch_groups(PGconn *conn, 
				 const struct electorate *elec,
				 struct group *groups);

/* Given the group information, return the candidate list */
extern struct cand_list *fetch_candidates(PGconn *conn, 
					  const struct electorate *elec,
					  struct group *groups);

/* Get all the ballots for this electorate */
extern struct ballot_list *fetch_ballots(PGconn *conn, 
					 const struct electorate *elec);

#endif /*_FETCH_H*/
