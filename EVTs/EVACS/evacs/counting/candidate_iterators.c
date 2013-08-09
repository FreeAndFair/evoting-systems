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

#include <assert.h>
#include <stdlib.h>
#include "hare_clark.h"
#include "candidate_iterators.h"

struct cand_list *new_cand_list(struct candidate *cand, struct cand_list *next)
{
	struct cand_list *ret;

	ret = malloc(sizeof(*ret));

	ret->cand = cand;
	ret->next = next;
	return ret;
}
	
/* Convenience iterators: */
struct cand_list *any_candidates(struct cand_list *from,
				 selectfn_t selectfn,
				 void *data)
{
	struct cand_list *i, *ret = NULL;
	unsigned int max_score = 1;

	for (i = from; i; i = i->next) {
		unsigned int score;

		score = selectfn(i->cand, data);
		if (score < max_score)
			continue;

		if (score > max_score) {
			/* Throw away old ones */
			free_cand_list(ret);
			ret = NULL;
			max_score = score;
		}
		/* Prepend new candidate */
		ret = new_cand_list(i->cand, ret);
	}

	return ret;
}

struct func_arg
{
	bool (*func)(struct candidate *, void *);
	void *data;
};

/* Dummy iterator: puts in the list if func returns true */
static unsigned int dummy_select(struct candidate *cand, void *data)
{
	struct func_arg *farg = data;
	if (farg->func(cand, farg->data)) return 1;
	else return 0;
}

/* Returns the number of candidates for whom func returned true */
unsigned int for_each_candidate(struct cand_list *from,
				bool (*func)(struct candidate *, void *),
				void *data)
{
	struct cand_list *list, *i;
	unsigned int ret;
	struct func_arg farg;

	farg.func = func;
	farg.data = data;

	list = any_candidates(from, dummy_select, &farg);
	/* Now count them */
	for (ret = 0, i = list; i; i = i->next)
		ret++;
	free_cand_list(list);
	return ret;
}

void free_cand_list(struct cand_list *list)
{
	struct cand_list *next;

	while (list) {
		next = list->next;
		free(list);
		list = next;
	}
}

struct candidate *extract_cand_destroy_list(struct cand_list *candlist)
{
	struct candidate *cand;

	assert(!candlist->next);

	cand = candlist->cand;
	free_cand_list(candlist);
	return cand;
}
