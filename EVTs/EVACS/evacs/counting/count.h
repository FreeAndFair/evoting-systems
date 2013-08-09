#ifndef _COUNT_H
#define _COUNT_H
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

/* Do a hare-clark scrutiny, until the candidate `vacating' reaches
   quota (if it's NULL, it will be a full scrutiny). */
void do_count(struct election *e,
	      struct ballot_list *ballots,
	      struct candidate *vacating);

/* Get the count number */
unsigned int get_count_number(void);

/* These are used by casual vacancy module */
/* Reset count number */
void reset_count(void);

/* Increment count number by one */
void increment_count(void);

/* Compare vote values between two piles */
int compare_vote_values(const void *ppile1, const void *ppile2);

/* Compare Total number of votes between two Candidates at Count */
int compare_candidate_totals(const void *candidate1, const void *candidate2);

/* Returns true if enough candidates over quota (ie. election finished),
   or vacating is successful. */
bool partial_exclusion(struct cand_list *candidates,
		       struct candidate *cand,
		       struct ballot_list *pile,
		       unsigned int num_seats,
		       unsigned int quota,
		       unsigned int partial_sum,
		       struct candidate *vacating,
		       bool is_last);

/* Excludes lowest candidate, maybe doing tiebreak. */
void exclude_candidate(struct cand_list *candidates,
		       unsigned int num_seats,
		       unsigned int quota,
		       struct candidate *vacating);

/* calculate the quota (majority) for a casual vacancy */
unsigned int calc_majority(struct cand_list *standing);

/* Join pile A and pile B */
struct ballot_list *join_piles(struct ballot_list *a,
			       struct ballot_list *b);

/* Routine to sum all the vote values in a pile, and return the
   truncated total */
unsigned int truncated_vote_sum(struct ballot_list *ballots);

/* Add votes for this count for the candidate to total. */
bool sum_total(struct candidate *cand, void *void_total);

/* Marks all candidates in 'candidates' as pending if they exceed quota.
	If 'vacating' is !NULL, and over quota, then it will return after marking
	'vacating' as pending. */
bool mark_pending_candidates(struct cand_list *candidates,
									  unsigned int quota,
									  struct candidate *vacating);

#endif /* _COUNT_H */
