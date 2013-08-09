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
#include "vote_in_progress.h"

static struct preference_set vote_in_progress =
{ .num_preferences = 0 };

/* DDSv2B-3.20: Delete Preference  */
void remove_pref(unsigned int pref_index)
{
	unsigned int i;
	for (i=pref_index; i < (vote_in_progress.num_preferences-1); i++) {
		vote_in_progress.candidates[i].db_candidate_index = 
			vote_in_progress.candidates[i+1].db_candidate_index;
		vote_in_progress.candidates[i].group_index =
			vote_in_progress.candidates[i+1].group_index;
		vote_in_progress.candidates[i].prefnum =
			vote_in_progress.candidates[i+1].prefnum;	
		
	}
	vote_in_progress.num_preferences--;		

}

/* DDS3.2.18: Remove Last Preference */
bool remove_last_pref(struct preference *undone_pref)
{
	if (vote_in_progress.num_preferences == 0)
		return false;
	/* DDS3.2.18: Decrement Last Preference Allocated */
	vote_in_progress.num_preferences--;

	*undone_pref = vote_in_progress.candidates
		[vote_in_progress.num_preferences];

	/* We don't need to do anything to explicitly remove the preference */
	return true;
}

/* Add a candidate with a specific preference number to the VIP */
void add_candidate_with_pref(unsigned int group_index,
			     unsigned int db_candidate_index,
			     unsigned int prefnum)
{
	/* DDS3.2.20: Store Preference */
	vote_in_progress.candidates[vote_in_progress.num_preferences]
		.group_index = group_index;
	vote_in_progress.candidates[vote_in_progress.num_preferences]
		.db_candidate_index = db_candidate_index;
	vote_in_progress.candidates[vote_in_progress.num_preferences]
		.prefnum = prefnum;

	/* DDS3.2.20: Increment Preference Number */
	vote_in_progress.num_preferences++;
	assert(vote_in_progress.num_preferences < PREFNUM_MAX);
}


/* Change the preference number of a candidate in the vote in progress */
void change_candidate_prefnum(unsigned int candidate_number, 
			      unsigned int new_pref)
{
	vote_in_progress.candidates[candidate_number].prefnum = new_pref;
}

void add_candidate(unsigned int group_index,
		   unsigned int db_candidate_index)
{
	/* Add one with the next number (for voting client, always in
           order) */
	add_candidate_with_pref(group_index, db_candidate_index,
				vote_in_progress.num_preferences+1);
}

/* DDS3.2.10: Delete Current Preferences */
void delete_prefs(void)
{
	/* DDS3.2.10: Delete Vote in Progress */
	/* DDS3.2.10: Delete Last Preference Number Allocated */
	vote_in_progress.num_preferences = 0;
}

/* Get a copy of the vote in progress */
const struct preference_set *get_vote_in_progress(void)
{
	return &vote_in_progress;
}

