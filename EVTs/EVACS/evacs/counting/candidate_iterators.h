#ifndef _CANDIDATE_ITERATORS_H
#define _CANDIDATE_ITERATORS_H
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

/* Iterators for working with candidate lists */
#include <stdbool.h>

struct candidate;
struct cand_list;

/* selectfn returns 0 for out of list, or otherwise only the highest
   return(s) will be returned */
typedef unsigned int (*selectfn_t)(struct candidate *, void *data);

/* Returns candidates for which selectfn returned highest non-zero number */
/* Caller must call free_cand_list on return value unless NULL. */
extern struct cand_list *any_candidates(struct cand_list *from,
					selectfn_t selectfn,
					void *data);

/* Returns count of number of candidates which func returned true */
extern unsigned int for_each_candidate(struct cand_list *from,
				       bool (*func)(struct candidate *, void*),
				       void *data);

/* Must call this after any_candidates() */
extern void free_cand_list(struct cand_list *list);

/* Return the (single) candidate from the list, and destroy the list */
extern struct candidate *extract_cand_destroy_list(struct cand_list *candlist);

/* Allocate a new candidate list node */
extern struct cand_list *new_cand_list(struct candidate *cand,
				       struct cand_list *next);
#endif /*_CANDIDATE_ITERATORS_H*/
