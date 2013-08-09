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

#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <stdlib.h>
#include <common/database.h>
#include "hare_clark.h"
#include "count.h"
#include "report.h"
#include "ballot_iterators.h"
#include "candidate_iterators.h"

/* Stuff we need for every count: starts empty */
static struct ballot_list *exhausted_ballots[MAX_COUNTS];

/* current count */
static unsigned int count;

/* count under consideration for comparison of total votes */
static unsigned int compare_count;

static unsigned int is_formal(struct ballot *ballot, void *ninf_void)
{
	unsigned int *num_informals = ninf_void;

	if (ballot->num_preferences == 0) {
		(*num_informals)++;
		return 0;
	}
	return 1;
}

static struct ballot_list *discard_informals(struct ballot_list *list)
{
	unsigned int num_informals = 0;
	struct ballot_list *formals;

	formals = any_ballots(list, &is_formal, &num_informals);
	report_informals(num_informals);

	/*	fprintf(stderr, "Freeing temp list\n");
		free_ballot_list(list);*/
	return formals;
}

static unsigned int calculate_quota(const struct electorate *elec,
				    const struct ballot_list *ballots)
{
	unsigned int quota;
	unsigned int num;

	num = number_of_ballots(ballots);
        /* hare-clarke */
	quota = (num / (elec->num_seats + 1)) + 1;
	report_quota(num, elec->num_seats, quota);

	return quota;
}

/* Calculate what a majority of votes is */
unsigned int calc_majority(struct cand_list *standing)
{
	unsigned int tva = 0;

	/* Calculate total votes available */
	for_each_candidate(standing, &sum_total, &tva);

	/* Majority is TVA/2 + 1 */
	return tva / 2 + 1;
}

static bool maybe_exclude(struct candidate *cand, void *unused)
{
	char *answer, c;

	printf("Candidate `%s' from `%s' [y/N]: ",
	       cand->name, cand->group->name);
	answer = fgets_malloc(stdin);

	c = answer[0];
	free(answer);
	if (toupper(c) == 'Y')
		cand->status = CAND_EXCLUDED;

	return false;
}

static void prompt_for_deceased(struct cand_list *candidates)
{
	char *answer;

	printf("Are any candidates deceased? [y/N]: ");
	answer = fgets_malloc(stdin);

	/* Nothing to do if no candidates deceased. */
	if (answer[0] != 'y' && answer[0] != 'Y') {
		free(answer);
		return;
	}

	printf("Please select deceased candidates:\n");

	/* Find out who it is: mark them EXCLUDED */
	for_each_candidate(candidates, maybe_exclude, NULL);
}

static bool mark_continuing(struct candidate *cand, void *unused)
{
	cand->status = CAND_CONTINUING;
	return false;
}

static bool set_vote_value(struct ballot *ballot, void *value)
{
	ballot->vote_value = *(struct fraction *)value;
	return false;
}

/* Return 1 if this candidate is the one mentioned in the preference */
static unsigned int match_pref(struct candidate *cand, void *void_npref)
{
	struct normalized_pref *npref = void_npref;

	if (npref->group_index == cand->group->group_index
	    && npref->db_candidate_index == cand->db_candidate_index)
		return 1;
	return 0;
}

bool sum_total(struct candidate *cand, void *void_total)
{
	unsigned int *total = void_total;

	*total += cand->c[get_count_number()].total;
	return false;
}

/* Routine to sum all the vote values in a pile, and return the
   truncated total */
unsigned int truncated_vote_sum(struct ballot_list *ballots)
{
	struct fraction sum = fraction_zero;
	struct ballot_list *i;

	for (i = ballots; i; i = i->next) {
		sum = fraction_add(sum, i->ballot->vote_value);
	}

	return fraction_truncate(sum);
}

/* SIPL 2011: The following was a nested function.
   As this is no longer supported by gcc, it has
   been brought to the top level and modified appropriately. */
/* This function is used by distribute_ballots()
   as a callback from for_each_ballot().
   The second parameter is the list of candidates. */
static bool distribute(struct ballot *ballot, void *candidates_pointer)
{
	unsigned int i,j=0;
	struct cand_list *candlist;
	struct candidate *cand;

	struct cand_list *candidates = (struct cand_list *)candidates_pointer;

        for (i = j; i < ballot->num_preferences; i++) {
		/* There should be only one which matches this */
		candlist = any_candidates(candidates, &match_pref,
					  &ballot->prefs[i]);
		/* if preference is for a non-standing candidate, skip it
		 (required for casual vacancy) */
		if (!candlist) continue;
		cand = extract_cand_destroy_list(candlist);

		if (cand->status == CAND_CONTINUING) {
			/* Prepend ballot to their pile */
			cand->c[count].pile
				= new_ballot_list(ballot,
						  cand->c[count].pile);
			ballot->count_transferred = count;
			return false;
		}
	}

	/* Vote is exhausted: prepend to exhausted pile */
	exhausted_ballots[count]
		= new_ballot_list(ballot,
				  exhausted_ballots[count]);
	return false;
}

static void distribute_ballots(struct ballot_list *ballots,
			       struct cand_list *candidates,
			       struct candidate *vacating)
{

	for_each_ballot(ballots, &distribute, (void *) candidates);
}

/* Update totals for this count for the candidate, unless it's "not_me". */
static bool update_total(struct candidate *cand, void *not_me)
{
	unsigned int sum;

	/* Skip the candidate they specify */
	if (cand == not_me)
		return false;

	sum = truncated_vote_sum(cand->c[count].pile);
	/* If count is 1, total at count = 0 was 0, so this still
           works */
	cand->c[count].total = cand->c[count-1].total + sum;

	report_ballots_transferred(count, cand->scrutiny_pos, cand->status,
				   number_of_ballots(cand->c[count].pile));
	report_votes_transferred(count, cand->scrutiny_pos, cand->status,
				 sum, cand->c[count].total);
	return false;
}

static void distribute_first_prefs(struct ballot_list *ballots,
				   struct cand_list *candidates,
				   struct candidate *vacating)
{
	report_transfer(count, fraction_one, number_of_ballots(ballots));
	distribute_ballots(ballots, candidates,vacating);
	if (! vacating) report_exhausted(count, 0, 0);
	for_each_candidate(candidates, &update_total, NULL);
	if (! vacating) report_lost_or_gained(count, 0);
}

static unsigned int made_quota(struct candidate *candidate, void *quota)
{
	/* If they are continuing and on or over quota, return total */
	if (candidate->status == CAND_CONTINUING
	    && candidate->c[count].total >= (unsigned int)quota)
		return candidate->c[count].total;
	else return 0;
}

/* Return true if this is the vacating candidate */
static bool mark_pending(struct candidate *candidate, void *vacating)
{
	candidate->status = CAND_PENDING;
	candidate->count_when_quota_reached = count;
	candidate->order_elected = increment_order_elected();
	/* if this is a casual vacancy, don't report them twice! */
	if (!vacating) report_pending(count, candidate->name);

	return (candidate == vacating);
}

/* Candidates need to be marked pending in order from HIGHEST down, so
   that report ordering is correct.
   Returns true if the candidate "vacating" has passed quota.
*/
bool mark_pending_candidates(struct cand_list *candidates,
									  unsigned int quota,
									  struct candidate *vacating)
{
	struct cand_list *pending;

	/* This will return the highest total CONTINUING candidate(s)
	   over quota */
	while ((pending = any_candidates(candidates, made_quota, (void*)quota))
	       != NULL) {
		/* Mark them pending */
		if (for_each_candidate(pending, mark_pending, vacating)) {
			/* Vacating candidate went over quota */
			free_cand_list(pending);
			return true;
		}
		free_cand_list(pending);
		/* Now loop and look for more */
	}
	return false;
}

static bool check_status(struct candidate *candidate, void *mask)
{
	return candidate->status & (unsigned)mask;
}

static unsigned int on_quota(struct candidate *candidate, void *quota)
{
	if (candidate->status == CAND_PENDING
	    && candidate->c[count].total == (unsigned int)quota) return 1;
	else return 0;
}

/* Mark the candidate elected at the given count */
static bool mark_elected(struct candidate *candidate, void *count_elected)
{
	candidate->status = CAND_ELECTED;
	report_elected((unsigned int)count_elected, candidate->scrutiny_pos);
	return false;
}

/* Mark the continuing candidates successful immediately in order of total votes*/
static bool elect_immediately(struct cand_list *candidates, unsigned int count_elected)
{
	unsigned int m,n=0;
	struct cand_list *i;
	struct candidate *elected[PREFNUM_MAX] = { NULL };

	/* build an array of successful candidates for sorting */
        for (i=candidates; i; i=i->next) {
		if (i->cand->status == CAND_CONTINUING)
			elected[n++] = i->cand;
	}

	/* Sort the successful candidates in descending order of total votes */
	compare_count = get_count_number();
	qsort(elected, n, sizeof(elected[0]), &compare_candidate_totals);

	for (m=0; m < n ; m++) {
		/* Go throught the motions so reporting is correct */
		mark_pending(elected[m], NULL);
		mark_elected(elected[m], &count_elected);
		/* If this candidate has a surplus, it will not be distributed
		   due to end of the election. ie. all vacancies filled */
		elected[m]->all_vacancies_filled_at_count=true;
	}
	return false;
}

static unsigned int over_quota_earliest(struct candidate *candidate,
					void *quota)
{
 	if (candidate->c[count].total > (unsigned int)quota) {
		assert(candidate->status == CAND_PENDING);
		/* Now, highest number wins, so invert value. */
		return INT_MAX - candidate->count_when_quota_reached;
	}
	else return 0;
}

static unsigned int match_name(struct candidate *candidate, void *name)
{
	if (strcasecmp(candidate->name, name) == 0)
		return 1;
	return 0;
}

static bool print_candidate(struct candidate *candidate, void *unused)
{
	printf("  %s (%s)\n", candidate->name, candidate->group->name);
	return false;
}

static struct candidate *prompt_for_tie(const char *reason,
					struct cand_list *candidates)
{
	struct cand_list *chosen_list;
	char *candname;

	printf("\nCandidate tiebreak required for %s at count %u:\n",
		reason, count);

	for_each_candidate(candidates, &print_candidate, NULL);

	do {
		printf("\nEnter name of candidate to select: ");
		candname = fgets_malloc(stdin);
		chosen_list = any_candidates(candidates, &match_name,candname);
	} while (!chosen_list);

	free(candname);
	return extract_cand_destroy_list(chosen_list);
}

static unsigned int total_at_count(struct candidate *candidate,
				   void *at_count)
{
	assert(candidate->status == CAND_PENDING);
	return candidate->c[(unsigned int)at_count].total;
}

/* Of these candidates, figure out whose surplus to distribute first */
static struct candidate *surplus_tiebreak(struct cand_list *candidates)
{
	unsigned int c;
	struct cand_list *winners;
	struct candidate *ret;

	/* More than one */
	assert(candidates->next);

	/* STEP 13 */
	for (c = count-1; c >= 1; c--) {
		winners = any_candidates(candidates, &total_at_count,
					 (void *)c);

		/* SIPL 2012-02-06 The return value of any_candidates()
		   can be NULL: if it is NULL,
		   then the remaining candidates are still tied,
		   but we reached a count in the countback where
		   they all have zero votes.  Treat this the same
		   as reaching the beginning of the count, i.e.,
		   go to a manual tie-break.
		   Without this test, the use of
		   winners->next below fails. */
		if (winners == NULL) {
			/* Break immediately here, so as not to
			   free candidates list. */
			break;
		}

		free_cand_list(candidates);

		/* Only one? */
		if (winners->next == NULL)
			return extract_cand_destroy_list(winners);
		/* Only continue to consider those who were equal top */
		candidates = winners;
	}

	/* STEP 14 */
	ret = prompt_for_tie("surplus distribution", candidates);
	free_cand_list(candidates);
	report_tiebreak(count, "surplus distribution", ret->name);

	/* STEP 15 */
	return ret;
}

/* Return the single "best" candidate for distribution */
static struct candidate *find_best(struct cand_list *candidates)
{
	struct cand_list *winners;
	unsigned int count_when_quota_reached;

	/* They all reached quota at the same time. */
	count_when_quota_reached = candidates->cand->count_when_quota_reached;

	/* Who had the highest total at that count? */
	winners = any_candidates(candidates, &total_at_count,
				 (void *)count_when_quota_reached);
	assert(winners);
	if (winners->next) {
		/* More than one: take to surplus_tiebreak. */
		/* surplus_tiebreak frees winners */
		return surplus_tiebreak(winners);
	}
	return extract_cand_destroy_list(winners);
}

/* Highest one "wins", but we know these are all under quota, so
   return quota - total */
static unsigned int lowest_at_count(struct candidate *candidate,
				    void *at_count)
{
	if (candidate->status != CAND_CONTINUING)
		return 0;

	/* We want to return a positive number, but highest for lowest total */
	return INT_MAX - candidate->c[(unsigned int)at_count].total;
}

/* Return the single "worst" candidate for elimination.  Frees
   candidate list. */
static struct candidate *exclude_tiebreak(struct cand_list *candidates)
{
	unsigned int c;
	struct cand_list *losers;
	struct candidate *ret;

	/* More than one */
	assert(candidates->next);

	/* STEP 16 */
	for (c = count-1; c >= 1; c--) {
		losers = any_candidates(candidates, &lowest_at_count,
					(void *)c);
		free_cand_list(candidates);

		/* Only one? */
		if (losers->next == NULL)
			return extract_cand_destroy_list(losers);
		/* Only continue to consider those who were equal bottom */
		candidates = losers;
	}

	/* STEP 17 */
	ret = prompt_for_tie("exclusion", candidates);
	free_cand_list(candidates);
	report_tiebreak(count, "exclusion", ret->name);

	/* STEP 18 */
	return ret;
}

static bool is_exhausted(struct ballot *ballot, void *candidates)
{
	unsigned int i;
	struct candidate *cand;

	for (i = 0; i < ballot->num_preferences; i++) {
		/* There should be only one which matches this */
		cand = extract_cand_destroy_list
			(any_candidates(candidates,
					&match_pref,
					&ballot->prefs[i]));

		/* Continuing candidate?  Not exhausted */
		if (cand->status == CAND_CONTINUING)
			return false;
	}

	/* Exhausted */
	return true;
}

/* SIPL 2011: The following was a nested function.
   As this is no longer supported by gcc, it has
   been brought to the top level and modified appropriately. */
/* This function is used by update_vote_values()
   as a callback from for_each_ballot().
   The second parameter is the new_vote_value. */
static bool update_vote_value(struct ballot *ballot,
			      void *new_vote_value_pointer)
{
  struct fraction new_vote_value = *((struct fraction *)new_vote_value_pointer);
	/* Ballot vote value may only DECREASE */
	if (fraction_greater(ballot->vote_value,new_vote_value))
		ballot->vote_value = new_vote_value;
	return false;
}

static void update_vote_values(struct ballot_list *ballots,
			       struct fraction new_vote_value)
{

	for_each_ballot(ballots, update_vote_value, &new_vote_value);
}

void reset_count(void)
{
	unsigned int i;

	count = 1;
	reset_order_elected();

	/* Also ensure that exhausted ballot piles are all empty */
	for (i = 0; i < MAX_COUNTS; i++) {
		free_ballot_list(exhausted_ballots[i]);
		exhausted_ballots[i] = NULL;
	}
}

unsigned int get_count_number(void)
{
	return count;
}

void increment_count(void)
{
	count++;
	fprintf(stderr,"\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
		"Starting Count %u",count);
}

/* Figure out how many votes this round (should always be same) */
static bool sum_totals(struct candidate *candidate, void *void_sum)
{
	unsigned int *votes_sum = void_sum;

	*votes_sum += candidate->c[count].total;
	return false;
}

/* Figure out how many ballots dealt with this round */
static bool sum_ballots(struct candidate *candidate, void *void_sum)
{
	unsigned int *ballots_sum = void_sum;

	*ballots_sum += number_of_ballots(candidate->c[count].pile);
	return false;
}

/* Calculate and report the total votes and total ballots at this count */
static void calculate_totals(struct cand_list *candidates)
{
	unsigned int total_sum = 0, ballot_sum;

	for_each_candidate(candidates, &sum_totals, &total_sum);
	ballot_sum = number_of_ballots(exhausted_ballots[count]);
	for_each_candidate(candidates, &sum_ballots, &ballot_sum);

	/* Reporting keeps track of totals lost/gained by fraction,
           and the total exhausted votes, so it adds them in for us */
	report_totals(count, total_sum, ballot_sum);
}


/* Figure out how many votes gained this round: (-ve if we're on the
   one who was just elected) */
static bool sum_gains(struct candidate *candidate, void *void_sum)
{
	int *votes_sum = void_sum;

	assert(count > 0);
	*votes_sum += candidate->c[count].total - candidate->c[count-1].total;
	return false;
}

/* Returns true as soon as the vacating candidate is over quota */
static void distribute_surplus(struct cand_list *candidates,
			       struct candidate *cand,
			       unsigned int quota,
			       struct candidate *vacating)
{
	unsigned int vote_value_of_surplus;
	unsigned int non_exhausted_ballots;
	int gain;
	struct fraction new_vote_value;
	struct ballot_list *pile;

	/* STEP 19 */
	/* We haven't incremented count yet, so this applies to NEXT count */
	mark_elected(cand, (void *)(count+1));

	/* STEP 20 */
	vote_value_of_surplus = cand->c[count].total - quota;

	/* STEP 21 */
	increment_count();

	/* STEP 22 */
	pile = cand->c[cand->count_when_quota_reached].pile;
	non_exhausted_ballots
		= (number_of_ballots(pile)
		   - for_each_ballot(pile, &is_exhausted, candidates));

	/* STEP 23 */
	if (non_exhausted_ballots == 0)
		new_vote_value = fraction_one;
	else
		new_vote_value = ((struct fraction) { vote_value_of_surplus,
                                                      non_exhausted_ballots });

	/* STEP 24 */
	update_vote_values(pile, new_vote_value);

	/* STEP 24b */
	/* Report actual value (may be capped) */
	report_transfer(count,
			pile->ballot->vote_value,
			vote_value_of_surplus);
	distribute_ballots(pile, candidates,vacating);
	cand->surplus_distributed = true;
	report_distribution(count, cand->name);
	report_distrib_from_count(count, cand->count_when_quota_reached);
	counting_raw_newline();


	/* STEP 25 */
	for_each_candidate(candidates, &update_total, cand);

	/* STEP 25a */
	if (mark_pending_candidates(candidates, quota, vacating))
		/* Vacating over quota: return immediately */
		return;

	/* STEP 26 */
	cand->c[count].total = quota;
	report_votes_transferred(count, cand->scrutiny_pos, cand->status,
				 quota - cand->c[count-1].total,
				 cand->c[count].total);

	/* STEP 27 */
	gain = 0;
	for_each_candidate(candidates, &sum_gains, &gain);
	report_lost_or_gained(count, gain);

	/* STEP 28 */
	for_each_ballot(exhausted_ballots[count], set_vote_value,
			(void *)&fraction_zero);
	report_exhausted(count,
			 number_of_ballots(exhausted_ballots[count]), 0);
	calculate_totals(candidates);
}

/* Compare vote values between two piles */
int compare_vote_values(const void *ppile1, const void *ppile2)
{
	const struct ballot_list *const *pp1 = ppile1;
	const struct ballot_list *const *pp2 = ppile2;

	/* None of these piles should be empty */
	assert((*pp1)->ballot);
	assert((*pp2)->ballot);

	/* qsort sorts in ascending order: we want descending order */
	return -fraction_compare((*pp1)->ballot->vote_value,
				 (*pp2)->ballot->vote_value);
}

/* Compare Total number of votes between two Candidates at Count */
/* Recurse (clumsily) if equal   */
int compare_candidate_totals(const void *candidate1, const void *candidate2)
{
	const struct candidate *const *cand1 = candidate1;
	const struct candidate *const *cand2 = candidate2;
	unsigned int t1 = (*cand1)->c[compare_count].total;
	unsigned int t2 = (*cand2)->c[compare_count].total;


	/* qsort sorts in ascending order: we want descending order */
	if (t1 > t2) return -1;
	if (t1 < t2) return 1;

	/* candidates equal at this count */
	if (compare_count ==0)
	/* candidates equal throughout scrutiny */
		return 0;

	/* compare previous count */
	compare_count--;
	return compare_candidate_totals(candidate1,candidate2);
}

/* Returns true if enough candidates over quota (ie. election finished),
   or vacating is successful. */
bool partial_exclusion(struct cand_list *candidates,
		       struct candidate *cand,
		       struct ballot_list *pile,
		       unsigned int num_seats,
		       unsigned int quota,
		       unsigned int pile_sum,
		       struct candidate *vacating,
		       bool is_last)
{
	int gain;

	/* STEP 36b */
	cand->c[count].total = cand->c[count-1].total -  pile_sum;
	report_votes_transferred(count, cand->scrutiny_pos, cand->status,
				 -pile_sum,  cand->c[count].total);

	/* STEP 37 */
	report_transfer(count, pile->ballot->vote_value, pile_sum);
	distribute_ballots(pile, candidates,vacating);
	report_exhausted(count,
			 number_of_ballots(exhausted_ballots[count]),
			 truncated_vote_sum(exhausted_ballots[count]));
	report_distribution(count, cand->name);

	/* STEP 38 */
	for_each_candidate(candidates, &update_total, cand);

	/* STEP 39 */
	gain = 0;
	for_each_candidate(candidates, &sum_gains, &gain);

	/* STEP 40, STEP 41 */
	gain += truncated_vote_sum(exhausted_ballots[count]);
	report_lost_or_gained(count, gain);

	if (is_last)
		report_fully_excluded(count, cand->name);
	else
		report_partially_excluded(count, cand->name);

	calculate_totals(candidates);

	/* STEP 42 */
	if (mark_pending_candidates(candidates, quota, vacating))
		return true;

	if (for_each_candidate(candidates, &check_status,
			       (void *)(CAND_ELECTED|CAND_PENDING))
	    == num_seats)
		return true;

	/* STEP 43 */
	return false;
}

/* For every count, if vote value is the same, report that as one of
   the sources of the votes being distrbuted */
static void calculate_ballot_source(struct fraction vote_value,
				    struct candidate *cand)
{
	unsigned int i;

	// For TIR 32, count has not been incremented yet, so we iterate to
	// count + 1
	for (i = 1; i < count+1; i++) {
		if (cand->c[i].pile
		    && (cand->c[i].pile->ballot->vote_value.numerator
			== vote_value.numerator)
		    && (cand->c[i].pile->ballot->vote_value.denominator
			== vote_value.denominator)) {
			/* Assign to *next* count: this is what we are
                           about to do */
			report_distrib_from_count(count+1, i);
		}
	}
	counting_raw_newline();
}

/* Join pile A and pile B */
struct ballot_list *join_piles(struct ballot_list *a,
			       struct ballot_list *b)
{
	struct ballot_list *i;

	if (!a)
		return b;

	/* Find last element */
	for (i = a; i->next; i = i->next);

	/* Join B to the end */
	i->next = b;
	return a;
}

/* SIPL 2011: The following was a nested function.
   As this is no longer supported by gcc, it has
   been brought to the top level and modified appropriately. */
/* This function is used by exclude_one_candidate()
   as a callback from for_each_ballot().
   The second parameter is the list of piles. */
static bool place_in_pile(struct ballot *ballot, void *piles_pointer)
{
  unsigned int i;
  bool new_pile = true;

  struct ballot_list **piles = (struct ballot_list **)piles_pointer;
  
  assert(ballot->count_transferred > 0);
  /* Find first empty pile, or that came in on same count. */
  
  for (i = 0; piles[i]; i++) {
    assert(i < (PREFNUM_MAX * MAX_COUNTS));
    
    if (piles[i]->ballot->count_transferred
	== ballot->count_transferred) {
      new_pile = false;
      break;
    }
  }

  /* Prepend to this pile */
  piles[i] = new_ballot_list(ballot, piles[i]);
  return new_pile;
}


/* Returns true if vacating is over quota, or finished because enough
   people are over quota to fill num_seats */
static bool exclude_one_candidate(struct cand_list *candidates,
				  struct candidate *cand,
				  unsigned int num_seats,
				  unsigned int quota,
				  struct candidate *vacating)
{
	unsigned int i;
	unsigned int used_piles;
	unsigned int pile_sum;
	/* Maximum number of vote piles == PREFNUM_MAX * MAX_COUNT
	 assuming PREFNUM_MAX candidates and a different vote_value
	at each count and all candidates continue until the last count.
	In practice there will be duplicate vote_values.*/
	struct ballot_list *piles[PREFNUM_MAX * MAX_COUNTS] = { NULL };

	/* STEP 30b */
	cand->status = CAND_BEING_EXCLUDED;

	/* STEP 31 */
	used_piles = 0;
	// For TIR 32, count has not been incremented yet, so we iterate to
	// count + 1
	for (i = 1; i <= count+1; i++)
		used_piles += for_each_ballot(cand->c[i].pile, place_in_pile,
					      piles);

	/* STEP 32 */
	qsort(piles, used_piles, sizeof(piles[0]), &compare_vote_values);
	for (i = 0; i < used_piles; i++) {
		/* Figure out where these ballots came from. */
		calculate_ballot_source(piles[i]->ballot->vote_value, cand);
		/* STEP 35 */
		increment_count();
		if (i == 0) report_excluded(count, cand->scrutiny_pos);

		/* All the piles with same vote value will now be
		   consecutive.  Add totals separately, and collapse
		   into one big pile for distribution. */
		/* STEP 36 */
		pile_sum = truncated_vote_sum(piles[i]);
		while (i + 1 < used_piles
		       && fraction_equal(piles[i]->ballot->vote_value,
					 piles[i+1]->ballot->vote_value)) {
			pile_sum += truncated_vote_sum(piles[i+1]);
			piles[i+1] = join_piles(piles[i], piles[i+1]);
			piles[i] = NULL;
			i++;
		}

		/* If we're finished, returning here will cause STEP 8
                   to finish the election. */
		if (partial_exclusion(candidates, cand, piles[i],
				      num_seats, quota, pile_sum, vacating,
				      i == used_piles-1))
			return true;
	}
	/* Catch corner case: no votes to distribute */
	if (used_piles == 0) {
		report_excluded(count+1, cand->scrutiny_pos);
		report_fully_excluded(count, cand->name);
	}

	/* STEP 33 */
	cand->status = CAND_EXCLUDED;

	return false;
}

/* Exclude the lowest candidate, maybe do tiebreak */
void exclude_candidate(struct cand_list *candidates,
		       unsigned int num_seats,
		       unsigned int quota,
		       struct candidate *vacating)
{
	struct cand_list *list;
	struct candidate *worst;

	/* Must return one candidate */
	list = any_candidates(candidates, &lowest_at_count, (void *)count);
	if (list->next != NULL)
		/* More than one: exclude_tiebreak frees list. */
		worst = exclude_tiebreak(list);
	else
		worst = extract_cand_destroy_list(list);

	exclude_one_candidate(candidates, worst, num_seats, quota, vacating);
}

/* Return final count, or when vacating reaches quota */
void do_count(struct election *e,
	      struct ballot_list *ballots,
	      struct candidate *vacating)
{
	unsigned int quota;

	/* STEP 1 */
	fprintf(stderr, "Discarding Informals:\t");
	ballots = discard_informals(ballots);

	/* STEP 2 */

	fprintf(stderr, "Calculating Quota\n");
	quota = calculate_quota(e->electorate, ballots);

	/* STEP 3 */
	for_each_candidate(e->candidates, &mark_continuing, NULL);
	prompt_for_deceased(e->candidates);

	/* STEP 4 */
	fprintf(stderr, "Setting initial vote_values\n");
	for_each_ballot(ballots, &set_vote_value, (void *)&fraction_one);

	/* STEP 5 */
	reset_count();

	/* STEP 6 */
	fprintf(stderr,"Distributing First Preferences\n");
	distribute_first_prefs(ballots, e->candidates, vacating);
	calculate_totals(e->candidates);

	/* STEP 7 */
	if (mark_pending_candidates(e->candidates, quota, vacating))
		/* Vacating candidate over quota */
		return;

	/* STEP 8 */
	while (for_each_candidate(e->candidates, &check_status,
				  (void *)(CAND_PENDING|CAND_ELECTED))
	       != e->electorate->num_seats) {
		struct cand_list *list;

		/* STEP 9 */
		if (for_each_candidate(e->candidates,
				       &check_status,
				       (void *)CAND_PENDING) == 0) {
			if (for_each_candidate(e->candidates,
					       &check_status,
					       (void *)
					       (CAND_ELECTED|CAND_CONTINUING))
			    == e->electorate->num_seats) {


				elect_immediately(e->candidates,get_count_number());
				/* Finish election */
				break;
			}
		}

		/* STEP 10 */
		list = any_candidates(e->candidates, &on_quota, (void *)quota);
		if (list != NULL) {
			/* Mark them elected on the NEXT count. */
			for_each_candidate(list, &mark_elected,
					   (void *)(count+1));
			free_cand_list(list);
			continue;
		}

		/* STEP 11 */
		list = any_candidates(e->candidates, &over_quota_earliest,
				      (void*)quota);
		if (list != NULL) {
			struct candidate *best;

			best = find_best(list);
			/* Hand best to distribute surplus. */
			distribute_surplus(e->candidates, best,quota,vacating);
			if (vacating && vacating->status == CAND_PENDING)
				return;
			free_cand_list(list);
			/* STEP 30 */
			continue;
		}

		/* STEP 12 */
		exclude_candidate(e->candidates,
				  e->electorate->num_seats,
				  quota, vacating);

		if (vacating && vacating->status == CAND_PENDING)
			return;
		/* STEP 34 */
	}

	/* Finished */
}
