#ifndef _HARE_CLARK_H
#define _HARE_CLARK_H
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
#include "fraction.h"

/* Electing a candidate only takes one round, but eliminating a
   candidate can, at worst, take as many turns as there are separate
   vote values.  Vote values change when candidates are elected (which
   may have happened num_seats-1 times), but they are cumulative, so
   we have 1 vote value the first time, 2 the second, 4 the third,
   etc.  So max number of vote values = 2 ^ (num_seats-1).

   So if we have to eliminate PREFNUM_MAX candidates (overestimate),
   and each elimination could take 2^(numseats-1): */
#define MAX_COUNTS (PREFNUM_MAX * (1 << (MAX_ELECTORATE_SEATS-1)))

enum cand_status
{
	/* Continuing */
	CAND_CONTINUING = 1,
	/* Successful */
	CAND_ELECTED = 2,
	/* Being excluded */
	CAND_BEING_EXCLUDED = 4,
	/* Lost */
	CAND_EXCLUDED = 8,
	/* Over quota, but not yet marked elected */
	CAND_PENDING = 16,
};

/* These preferences are implicitly indexed: ie. first is 1, second is
   2, etc */
struct normalized_pref
{
	unsigned int group_index;
	unsigned int db_candidate_index;
};

/* A single ballot paper */
struct ballot
{
	/* The "vote value" of this ballot */
	struct fraction vote_value;

	/* The count at which this ballot last transferred */
	unsigned int count_transferred;

	/* Preferences hang off end. */
	unsigned int num_preferences;
	struct normalized_pref prefs[0];
};

/* List/pile of ballot papers */
struct ballot_list
{
	struct ballot_list *next;

	/* The ballot */
	struct ballot *ballot;
};

struct group
{
	/* Who are we? */
	char *name;
        char *abbrev;
	unsigned int group_index;
};

struct candidate
{
	/* Who am I? */
	unsigned int db_candidate_index;
	char *name;
	struct group *group;

	/* Where am I on the scrutiny sheet? */
	unsigned int scrutiny_pos;

	/* How am I going? */
	enum cand_status status;

	/* If status is PENDING or ELECTED, when did I reach it? */
	unsigned int count_when_quota_reached;

	/* When  elected, I was the n'th elected */
	unsigned int order_elected;

	/* Has my surplus been distributed? */
	bool surplus_distributed;
	
	/* When elected, were all vacancies filled on that count? */
	bool all_vacancies_filled_at_count;

	struct {
		/* My pile of votes, for every count. */
		struct ballot_list *pile;

		/* My totals, for every count */
		unsigned int total;
	} c[MAX_COUNTS];
};

struct cand_list
{
	struct cand_list *next;

	/* The candidate */
	struct candidate *cand;
};

struct election
{
	/* The electorate */
	char *title;

	/* std preferential election sequence (one for each vacancy)*/
	unsigned int election_number;

	/* details of electorate being counted*/
	struct electorate *electorate;

	/* The canonical candidates */
	struct cand_list *candidates;

	/* The actual number of groups */
	unsigned int num_groups;

	/* Room for one per preference */
	struct group groups[PREFNUM_MAX];
};
#endif /*_HARE_CLARK_H*/
