/* This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd */

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

/***************************************************************
  Refer to the <project base dir>/devel/doc/hare-clark.doc file
  for a detailed description of the Hare Clarke algorithm.
 ***************************************************************/

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <common/database.h>
#include "hare_clark.h"
#include "fetch.h"
#include "report.h"
#include "ballot_iterators.h"
#include "candidate_iterators.h"
#include "count.h"

/* Get electorate */
static struct electorate *prompt_for_electorate(PGconn *conn)
{
	char *name;
	struct electorate *elec;

	do {
		printf("Please enter the electorate name to count: ");
		name = fgets_malloc(stdin);
		elec = fetch_electorate(conn, name);
		if (!elec)
			printf("Electorate `%s' not found!\n", name);
		free(name);
	} while (!elec);

	return elec;
}

static bool prompt_for_new_vacancy()
{
	char *answer;

	printf("Another Casual Vacancy for this electorate? [n/Y]: ");
	answer = fgets_malloc(stdin);

	/* Nothing to do if no candidates deceased. */
	if (answer[0] != 'n' && answer[0] != 'N') {
		free(answer);
		return true;
	} else {
		free(answer);
		return false;
	}

}


static unsigned int match_name(struct candidate *cand, void *name)
{
	if (strcasecmp(cand->name, name) == 0) return 1;
	return 0;
}

/* Get vacating candidate */
static struct candidate *vacating_candidate(struct cand_list *candidates)
{
	struct cand_list *ret;
	char *name;

	do {
		printf("Please enter the vacating candidate name: ");
		name = fgets_malloc(stdin);

		ret = any_candidates(candidates, &match_name, name);
		if (!ret)
			printf("Unknown candidate `%s'\n", name);
		free(name);
	} while (!ret);

	return extract_cand_destroy_list(ret);
}

static bool free_piles(struct candidate *cand, void *unused)
{
	unsigned int i;

	for (i = 0; i < MAX_COUNTS; i++)
		if (cand->c[i].pile)
			free_ballot_list(cand->c[i].pile);

	return false;
}

static bool free_candidate(struct candidate *cand, void *unused)
{
	free(cand->name);
	free(cand);
	return false;
}

static void free_group_names(struct group *groups, unsigned int num_groups)
{
	unsigned int i;

	for (i = 0; i < num_groups; i++)
		free(groups[i].name);
}

static unsigned int selected(struct candidate *cand, void *vacating)
{
	char *answer;

	/* The vacating candidate is included in the count */
	if (cand == vacating) return 1;

	/* Elected or pending already have seats */
	if (cand->status == CAND_PENDING || cand->status == CAND_ELECTED)
		return 0;

	printf("Candidate `%s' from `%s' [y/N]: ",
	       cand->name, cand->group->name);
	answer = fgets_malloc(stdin);
	if (toupper(answer[0]) == 'Y') {
		free(answer);
		/* Reset their status to CONTINUING */
		cand->status = CAND_CONTINUING;
		return 1;
	}
	free(answer);
	return 0;
}

/* Create list of all candidates standing (and vacating one) */
static struct cand_list *get_standings(struct cand_list *all,
				       struct candidate *vacating)
{
	struct cand_list *i, *reverse_order, *ballot_order;
	unsigned int j;

	/* side effect - order is reversed */
	reverse_order=any_candidates(all, &selected, vacating);

	/* re-reverse back into H-C ballot order */
        ballot_order = NULL;
	for(i=reverse_order, j=0; i; i=i->next, j++) {
		ballot_order=new_cand_list(i->cand,
					   ballot_order);
		ballot_order->cand->scrutiny_pos = j;
	}

	return ballot_order;
}

static bool clear_candidate(struct candidate *candidate, void *vacating)
{
	unsigned int i;
	if (candidate == vacating) return false;
	printf("Position %u: %s                                 "
	       "\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
	       "\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
	       "\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b",
	       candidate->scrutiny_pos, candidate->name);
	fflush(stdout);
	/* Candidate is now back to continuing, not on quota */
	candidate->status = CAND_CONTINUING;
	candidate->count_when_quota_reached = 0;
	/* Clear totals and ballot piles */
	for (i = 0; i < MAX_COUNTS; i++) {
		candidate->c[i].total = 0;
		free_ballot_list(candidate->c[i].pile);
		candidate->c[i].pile = NULL;
	}
	return false;
}

static bool matches(struct candidate *candidate,
		    struct normalized_pref *pref)

{
	if ( pref->group_index == candidate->group->group_index
	    && pref->db_candidate_index == candidate->db_candidate_index)
		return true;
	return false;
}

/* SIPL 2011: Commented out the following function,
   because it is not used (and therefore generated a
   compiler warning).
static void dump_prefs(struct ballot *ballot,
		       struct cand_list *candidates)
{
	unsigned int i;
	struct candidate *cand;
	struct cand_list *matched;

	for (i=0; i < ballot->num_preferences; i++) {
		matched = (struct cand_list *)
			any_candidates(candidates,
				       (selectfn_t)&matches,
				       &ballot->prefs[i]);
		if (matched) {
			if (matched->next) {
				while (matched->next) {
					printf("%u:\t%s\n",i,matched->cand->name);
					matched = matched->next;
				}
			} else {
				cand = extract_cand_destroy_list(matched);
				printf("%u:\t%s\n",i,cand->name);
			}
		} else {
			printf("%u:\tNOT STANDING\n",i);
		}
	}

}
*/

/* Return true if the ballot is exhausted */
static bool is_exhausted(struct ballot *ballot,
			 void *candidates)
{
	unsigned int h,i;
	struct candidate *vacating;
	struct cand_list *j,*k,*candidate_list;

	candidate_list = candidates;
	/* retrieve vacating candidate (last on list)*/
	for (j=candidates; j->next ;j=j->next,k=j);
	vacating = j->cand;

	/* First find candidate on ballot */
	for (i = 0; !matches(vacating, &ballot->prefs[i]); i++) {
		/* Candidate must be on ballot for it to be in her pile */
		assert(i < ballot->num_preferences);
	}

	/* Last choice?  If so, it's now exhausted */
	if (i == ballot->num_preferences-1)
		return true;

  /* is there a later choice for a candidate still standing (during H-C)??  */
	for(h=i+1; h <  ballot->num_preferences ; h++) {
		if ( any_candidates(candidates,
				    (selectfn_t)&matches,
				    &ballot->prefs[h]))
			/* Yes, so ballot not exhausted */
			return false;
	}
	/* no match - ballot is exhausted */
	return true;
}

/* Routine to sum all the vote values in a pile, and return the
   truncated total */
static struct fraction vote_sum(struct ballot_list *ballots)
{
	struct fraction sum = fraction_zero;
	struct ballot_list *i;

	for (i = ballots; i; i = i->next) {
		sum = fraction_add(sum, i->ballot->vote_value);
	}

	return sum;
}

/* Return true if the ballot is not exhausted */
static bool not_exhausted(struct ballot *ballot, void *vacating)
{
	return !is_exhausted(ballot, vacating);
}

static bool set_vote_value(struct ballot *ballot, void *value)
{
	ballot->vote_value = *(struct fraction *)value;
	return false;
}

/* These are the ballots received at the vacating member's successful count:
   return the non-exhausted ones, with their value altered.
 */
static struct ballot_list *
alter_value_nonexhausted(struct ballot_list *piles[0],
			 unsigned int *num_piles,
			 struct cand_list *candidates,
			 unsigned int count,
			 unsigned int quota,
			 struct ballot_list *ballots,
			 unsigned int num_seats)
{
	unsigned int ncp, n, ncp_by_tv;
	struct candidate *vacating;
	struct cand_list *i;

	struct ballot_list *exhausted, *nonexhausted;
	struct fraction tv;

	/* vacating candidate last in linked list */
	for (i=candidates; i->next ;i=i->next);
	vacating = i->cand;

	/* STEP 4 */
	nonexhausted = any_ballots(ballots, (void *)&not_exhausted, candidates);
	exhausted = any_ballots(ballots, (void *)&is_exhausted, candidates);

	/* N: number of votes at previous count (if any)*/
	n = vacating->c[count-1].total;


	/* In the case where the vacating candidate was elected over quota,
	   but their surplus was not distributed because all vacancies were
	   filled, all ballots are considered exhausted and distributed with
	   the same vote value , regardless of any other continuing candidates */
	if (((number_of_ballots(ballots) + n) > quota &&
	    vacating->surplus_distributed == false) &&
	    (vacating->all_vacancies_filled_at_count == true ||
		    vacating->order_elected == num_seats)) {
		exhausted = join_piles(exhausted, nonexhausted);
		nonexhausted = NULL;
	}

	/* NCP: number of ballots without a next avail. preference */
	ncp = number_of_ballots(exhausted);

	/* TV: transfer value of ballots */
	tv = ballots->ballot->vote_value;

	/* STEP 5 */
	/* NCP x TV (truncated, but doesn't matter) */
	ncp_by_tv = (ncp * tv.numerator) / tv.denominator;

	/* STEP 6 */
	if ((int) ncp_by_tv >=  (int) ((int) quota - (int) n)) {
		/* Clause 4.3 13 (2) */
		struct fraction value;

		/* STEP 7 */
		/* Exhausted ballots get value: (Q-N)/NCP */
		value = ((struct fraction){ quota - n,
					    ncp });
		for_each_ballot(exhausted, &set_vote_value, &value);
		report_exhausted(0, number_of_ballots(exhausted),
				 fraction_truncate(vote_sum(exhausted)));
		if (exhausted)
			piles[(*num_piles)++] = exhausted;

		/* Non-exhausted ballots get value: 0 */
		for_each_ballot(nonexhausted, &set_vote_value,
				(void *)&fraction_zero);
	} else {
		/* Clause 4.3 13 (3) */
		struct fraction value;

		/* STEP 8 */
		/* Exhausted ballots unchanged value */
		report_exhausted(0, number_of_ballots(exhausted),
				 fraction_truncate(vote_sum(exhausted)));
		if (exhausted)
			piles[(*num_piles)++] = exhausted;

		/* Non-exhausted: (Q - N - (NCP x TV)) / CP */
		value = ((struct fraction){ quota - n - ncp_by_tv,
					    number_of_ballots(nonexhausted) });
		for_each_ballot(nonexhausted, &set_vote_value, &value);
	}

	return nonexhausted;
}


static bool set_scrutiny_pos(struct candidate *cand, void *pos)
{
	int *i = pos;

	cand->scrutiny_pos = *i;
	(*i)++;

	return false;
}


static bool has_majority(struct candidate *cand, void *standing)
{
	unsigned int majority;

	majority = calc_majority(standing);

	/* On or equal to majority */
	if (cand->c[get_count_number()].total >= majority)
		return true;
	return false;
}

static bool is_continuing(struct candidate *cand, void *vacating)
{
  if ((vacating != NULL)  && (cand == vacating))
	 return true;

	if (cand->status == CAND_CONTINUING)
		return true;
	else
		return false;
}

int main(int argc, char *argv[])
{
	struct ballot_list *ballots;
	PGconn *conn;
	struct election e;
	unsigned int i, final_count, quota, num_piles, temp, total, pile_sum;
	unsigned int ballots_counted;
	struct candidate *vacating;
	struct cand_list *standing, *hc_standing, *winner, *cands_plus_vac;
	char *title;
	struct ballot_list *piles[MAX_COUNTS] = { NULL };
	bool overquota;

	/* Get the information we need */
	conn = connect_db(DATABASE_NAME);
	if (!conn) bailout("Can't connect to database:'%s':\n\t%s\n",
			   DATABASE_NAME,PQerrorMessage(conn));

	e.electorate = prompt_for_electorate(conn);

	fprintf(stderr,"Fetching Ballots: ");
	ballots = fetch_ballots(conn, e.electorate);

	do {
		e.num_groups = fetch_groups(conn, e.electorate, e.groups);
		e.candidates = fetch_candidates(conn, e.electorate, e.groups);
		vacating = vacating_candidate(e.candidates);

		/* Start the reporting (we will discard these) */
		/* STEP 1 */
		report_start(&e, NULL);
		fprintf(stderr,"Running Hare-Clark count for %s\n",e.electorate->name);
		do_count(&e, ballots, vacating);
		quota = report_get_quota();
		final_count = get_count_number();

		report_end(final_count, "");

		if (vacating->status != CAND_PENDING
		    && vacating->status != CAND_ELECTED)
			bailout("Sorry, that candidate was not elected!\n");

		cands_plus_vac = new_cand_list(malloc(sizeof(struct candidate)), e.candidates);

		cands_plus_vac->cand = vacating;

		/* Ensure all candidates over quota are marked as pending so correct
			transfer value is calculated - do_count bails when vacating goes
			over quota.  If another candidate goes over quota on the same count, but with
			a lower total he/she will not be marked as pending. */
		mark_pending_candidates(cands_plus_vac, quota, NULL);

		hc_standing = any_candidates(cands_plus_vac,(void *)&is_continuing,vacating);

		/* Collect all the piles of ballots from vacating candidate:
		   sum them while we're at it. */
		/* STEP 3 */
		printf("\nCollecting Ballots\n");
		total = 0;
		for (i = 0; i <= final_count; i++)
			total += fraction_truncate(vote_sum(vacating->c[i].pile));
		overquota=false;
		if (total > quota) {
			overquota=true;
			total=quota;
		}

		/* STEP 4 */
		/* Alter the value of the final count ballots
		   ONLY IF VACATING CANDIDATE WAS OVER QUOTA*/
		if (overquota == true) {
			/* Leave the final pile to be altered */
			for (num_piles = i = 0; i < final_count; i++) {
				if (vacating->c[i].pile) {
					piles[num_piles++] = vacating->c[i].pile;
					vacating->c[i].pile = NULL;
				}
			}

			/*  *MAY* separate exhausteds into their own pile */
			temp=num_piles; num_piles++;
			piles[temp]
				=alter_value_nonexhausted(piles,
							  &num_piles,
							  hc_standing,
							  final_count,
							  quota,
							  vacating->c[final_count].pile,
							  e.electorate->num_seats);
			if (number_of_ballots(piles[temp]) == 0) {
				/* All ballots exhausted, remove pile*/
				piles[temp]=piles[--num_piles];
			}
			vacating->c[final_count].pile = NULL;
		} else {
			/* get ALL piles, including the final count pile*/
			for (num_piles = i = 0; i <= final_count; i++) {
				if (vacating->c[i].pile) {
					piles[num_piles++] = vacating->c[i].pile;
					vacating->c[i].pile = NULL;
				}
			}
		}

		/* Now we are up to the count where the vacating calculation begins */
		printf("\nPlease select the candidates who are standing:\n");
		standing = get_standings(e.candidates, vacating);
		printf ("--------------------------------------------------------------"
			"---------------\n\n");


		/* Start with the fresh candidates */
		/* STEP 2 */
		printf("Resetting Scrutiny\n");
		free_cand_list(e.candidates);
		e.candidates = standing;

		/* Reset positions on scrutiny sheet.*/
		i=0;
		for_each_candidate(standing, &set_scrutiny_pos, &i);

		/* Start a new report */
		report_start(&e, vacating);

		/* STEP 9 */
		/* Sort piles into vote value order */
		printf("Sorting Ballots by Vote Value\n");
		qsort(piles, num_piles, sizeof(piles[0]), &compare_vote_values);

		/* STEP 10 */
		reset_count();

		/* STEP 11 */
		printf("Freeing ballot memory from Hare Clark counts\n");
		for_each_candidate(standing, &clear_candidate, NULL);
		printf("\nDone\n");
		/* Complete the partial exclusions for the vacating candidate */
		/* STEP 12 */
		vacating->c[0].total = total;
		/* STEP 13 */
		vacating->status = CAND_BEING_EXCLUDED;
		report_vacancy_total_votes(total);

		/* STEP 14 */
		ballots_counted = 0;
		for (i = 0; i < num_piles; i++) {
			/* All the piles with same vote value will now be consecutive.
			   Add totals separately, and collapse each group of equal vote
			   value into one big pile for distribution. */
			pile_sum = truncated_vote_sum(piles[i]);
			while (i + 1 < num_piles
			       && fraction_equal(piles[i]->ballot->vote_value,
						 piles[i+1]->ballot->vote_value)) {
				pile_sum += truncated_vote_sum(piles[i+1]);
				piles[i+1] = join_piles(piles[i], piles[i+1]);
				piles[i] = NULL;
				i++;
			}
			ballots_counted += number_of_ballots(piles[i]);
			report_vacancy_total_ballots(ballots_counted);
			/* Do the partial exclusion (infinite quota: we always
			   finish this exclusion process) */
			partial_exclusion(standing, vacating, piles[i],
									1, UINT_MAX, pile_sum, vacating,
									i == num_piles-1);
			/* Don't increment count the last time:
			   exclude_candidate does that */
			if (i != num_piles - 1) increment_count();
			free_ballot_list(piles[i]);
		}

		/* If noone has a majority... */
		report_majority(get_count_number(), calc_majority(standing));

		/* STEP 15 */
		while (!(winner = any_candidates(standing, (void *)&has_majority, standing))) {
			exclude_candidate(standing, 1, UINT_MAX, vacating);
			report_majority(get_count_number(), calc_majority(standing));
		}

		/* STEP 16 */
		/* Report who was elected (can only be one) */
		assert(winner->next == NULL);
		reset_order_elected();
		increment_order_elected();
		report_pending(get_count_number(), winner->cand->name);
		title = sprintf_malloc("the Casual Vacancy of %s",
				       vacating->name);

		report_end(get_count_number(), title);

		for_each_candidate(e.candidates, &free_candidate, NULL);
		for_each_candidate(e.candidates, &free_piles, NULL);
		free_group_names(e.groups, e.num_groups);
		/*  free_electorates(e.electorate);*/

		fprintf(stderr,"\nPrinting Scrutiny\n");
		system((const char*) "/opt/eVACS/bin/print_scrutiny.sh");

	} while (prompt_for_new_vacancy() == true);

	PQfinish(conn);

	return 0;
}
