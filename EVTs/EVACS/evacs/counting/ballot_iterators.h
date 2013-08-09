#ifndef _BALLOT_ITERATORS_H
#define _BALLOT_ITERATORS_H
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

/* Iterators for working with ballots */
#include <stdbool.h>

struct ballot_list;
struct ballot;

/* selectfn returns 0 for out of list, or otherwise only the highest
   return(s) will be returned */
typedef unsigned int (*ballot_selectfn_t)(struct ballot *, void *data);

/* Returns ballots for which selectfn returned highest non-zero number */
/* Caller must call free_ballot_list on return value unless NULL. */
extern struct ballot_list *any_ballots(struct ballot_list *from,
				       ballot_selectfn_t selectfn,
				       void *data);

/* Returns count of number of ballots which func returned true */
extern unsigned int for_each_ballot(struct ballot_list *from,
				    bool (*func)(struct ballot *, void *),
				    void *data);

/* Returns the number of ballots */
extern unsigned int number_of_ballots(const struct ballot_list *from);

/* Must call this after any_ballots() */
extern void free_ballot_list(struct ballot_list *list);

/* Create a new ballot list */
extern struct ballot_list *new_ballot_list(struct ballot *ballot,
					   struct ballot_list *next);
#endif /*_BALLOT_ITERATORS_H*/
