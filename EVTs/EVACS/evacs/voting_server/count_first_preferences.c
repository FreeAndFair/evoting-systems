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
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <stdlib.h>
#include <common/database.h>
#include "display_first_preferences.h"
#include "count_first_preferences.h"
#include <counting/ballot_iterators.h>
#include <counting/candidate_iterators.h>

/* Stuff we need for every count: starts empty */
static struct ballot_list *exhausted_ballots[MAX_COUNTS];

/* current count */
static unsigned int count;

static unsigned int is_formal(struct ballot *ballot, void *ninf_void)
{
  unsigned int *num_informals = ninf_void;

  if (ballot->num_preferences == 0) {
    (*num_informals)++;
    return 0;
  }
  return 1;
}

static struct ballot_list *discard_informals(struct ballot_list *list,
     /* SIPL 2011: Changed parameter type to match other occurrences. */
					     /* int *num_informals) */
					     unsigned int *num_informals)
{
  struct ballot_list *formals;

  *num_informals = 0;

  formals = any_ballots(list, &is_formal, num_informals);

  return formals;
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

  for_each_ballot(ballots, &distribute, (void *)candidates);
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

  return false;
}

static void distribute_first_prefs(struct ballot_list *ballots,
				   struct cand_list *candidates,
				   struct candidate *vacating)
{
  distribute_ballots(ballots, candidates,vacating);
  for_each_candidate(candidates, &update_total, NULL);
}

/* SIPL 2011: Commented out the following function, because it is never used. */
/* static unsigned int made_quota(struct candidate *candidate, void *quota) */
/* { */
/*   /\* If they are continuing and on or over quota, return total *\/ */
/*   if (candidate->status == CAND_CONTINUING  */
/*       && candidate->c[count].total >= (unsigned int)quota) */
/*     return candidate->c[count].total; */
/*   else return 0; */
/* } */

/* SIPL 2011: Commented out the following function, because it is never used. */
/* Return true if this is the vacating candidate */
/* static bool mark_pending(struct candidate *candidate, void *vacating) */
/* { */
/*   candidate->status = CAND_PENDING; */
/*   candidate->count_when_quota_reached = count; */
/*   /\* if this is a casual vacancy, don't report them twice! *\/ */
	
/*   return (candidate == vacating); */
/* } */

void reset_count(void)
{
  unsigned int i;

  count = 1;
	
  /* Also ensure that exhausted ballot piles are all empty */
  for (i = 0; i < MAX_COUNTS; i++) {
    free_ballot_list(exhausted_ballots[i]);
    exhausted_ballots[i] = NULL;
  }
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
}

#define DIVIDER_LINE "--------------------------------------------------------------------------------\n"

static struct group *last_group = NULL;

static bool print_first_preference(struct candidate *cand, void *unused)
{
  if(last_group != cand->group) {
    // 65 = ASCII "A"
    printf(DIVIDER_LINE);
    printf(" %c %s\n", cand->group->group_index + 65, cand->group->name);
    printf(DIVIDER_LINE);
    last_group = cand->group;
  }
  printf("   %36.36s %7u\n", cand->name, cand->c[1].total);
  return true;
}

/* SIPL 2011: Added indication of either pre-poll or polling day 
 *            after electorate names.  This is the new parameter
 *            "qualification".  The possible values are defined in
 *            display_first_preferences.h.
 *            The value is here converted to a string, and
 *            displayed in parentheses after the electorate name.
 */
/* Count first preferences */
void do_count(struct election *e,
	      struct ballot_list *ballots,
	      struct candidate *vacating,
	      const int qualification)
{
  unsigned int total_ballots = 0;
  unsigned int num_informals = 0;
  struct ballot_list *i;

  for(i = ballots; i; i = i->next) {
    total_ballots++;
  }

  printf(DIVIDER_LINE);
  printf("Electorate: %s (%s)\n", e->electorate->name,
         qualification_names[qualification]);
  printf(DIVIDER_LINE);

  /* If there are less than 20 votes, we do not display the preference
     summary */
  if (total_ballots < 20) {
    printf("There are only %u ballots, preference summary will not be displayed\n", total_ballots);
    printf(DIVIDER_LINE);
    return;
  }

  /* STEP 1 */
  ballots = discard_informals(ballots, &num_informals);

  /* STEP 3 */
  for_each_candidate(e->candidates, &mark_continuing, NULL);

  /* STEP 4 */
  for_each_ballot(ballots, &set_vote_value, (void *)&fraction_one);

  /* STEP 5 */
  reset_count();

  /* STEP 6 */
  distribute_first_prefs(ballots, e->candidates, vacating);
  calculate_totals(e->candidates);

  for_each_candidate(e->candidates, &print_first_preference, NULL);

  printf(DIVIDER_LINE);
  printf("Informal Votes:                               %u\n", num_informals);
  printf("Total Votes:                                  %u\n", total_ballots);
  printf(DIVIDER_LINE);
}
