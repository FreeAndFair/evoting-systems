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

#include <stdlib.h>
#include "hare_clark.h"
#include "ballot_iterators.h"

struct ballot_list *new_ballot_list(struct ballot *ballot,
				    struct ballot_list *next)
{
	struct ballot_list *ret;

	ret = malloc(sizeof(*ret));

	ret->ballot = ballot;
	ret->next = next;
	return ret;
}
	
/* Convenience iterators: */
struct ballot_list *any_ballots(struct ballot_list *from,
				ballot_selectfn_t selectfn,
				void *data)
{
	struct ballot_list *i, *ret = NULL;
	unsigned int max_score = 1;

	for (i = from; i; i = i->next) {
		unsigned int score;

		score = selectfn(i->ballot, data);
		if (score < max_score)
			continue;

		if (score > max_score) {
			/* Throw away old ones */
			free_ballot_list(ret);
			ret = NULL;
			max_score = score;
		}
		/* Prepend new ballot */
		ret = new_ballot_list(i->ballot, ret);
	}

	return ret;
}

struct func_arg
{
	bool (*func)(struct ballot *, void *);
	void *data;
};

/* Dummy iterator: puts in the list if func returns true */
static unsigned int dummy_select(struct ballot *ballot, void *data)
{
	struct func_arg *farg = data;
	if (farg->func(ballot, farg->data)) return 1;
	else return 0;
}

/* Returns the number of ballots for whom func returned true */
unsigned int for_each_ballot(struct ballot_list *from,
			     bool (*func)(struct ballot *, void *),
			     void *data)
{
	struct ballot_list *list, *i;
	unsigned int ret;
	struct func_arg farg;

	farg.func = func;
	farg.data = data;

	list = any_ballots(from, dummy_select, &farg);
	/* Now count them */
	for (ret = 0, i = list; i; i = i->next)
		ret++;
	free_ballot_list(list);
	return ret;
}

/* Returns the number of ballots */
unsigned int number_of_ballots(const struct ballot_list *from)
{
	unsigned int i;

	for (i = 0; from; from = from->next)
		i++;

	return i;
}

void free_ballot_list(struct ballot_list *list)
{
	struct ballot_list *next;

	while (list) {
		next = list->next;
		free(list);
		list = next;
	}
}
