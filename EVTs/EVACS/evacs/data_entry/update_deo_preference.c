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
#include <common/cursor.h>
#include <common/ballot_contents.h>
#include <voting_client/vote_in_progress.h>
#include <voting_client/get_rotation.h>
#include <voting_client/main_screen.h>
#include <voting_client/draw_group_entry.h>
#include "move_deo_cursor.h"
#include "delete_deo_preference.h"

#include "update_deo_preference.h"


/* DDS3.18: Insert Preference Digit */
void insert_preference_digit(unsigned int group_index, unsigned int dbci, 
			     unsigned int pref)
{
	int i;
	bool found = false;
	unsigned int new_pref;
	const struct preference_set *vip;

	vip = get_vote_in_progress();
	
	/* Check if candidate already given a preference number */
	for (i=0; i < vip->num_preferences; i++) {
		if ((vip->candidates[i].group_index == group_index) 
		    && (vip->candidates[i].db_candidate_index == dbci)) {
			/* Can only occur once */
			assert(found == false);
			found = true;
			if (vip->candidates[i].prefnum != 0) {
				/* new digit inserted at right of current pref 
				   number, with most significant digit removed
				   if more than 2 digits */
				new_pref = (vip->candidates[i].prefnum 
					    * 10 + pref) % 100;
				if (new_pref > 0) {
				        change_candidate_prefnum(i, new_pref);
				} else {
				        delete_deo_preference();
				}
			}
			else {
				change_candidate_prefnum(i, pref);
			}
		}
	}
	if (!found) {
		/* Add candidate and preference to the Vote in Progress */
	        if (pref > 0) {
		      add_candidate_with_pref(group_index, dbci, pref);
	        }
	}
}



/* DDS3.18: Update DEO Preference */
void update_deo_preference(unsigned int pref)
{
	struct cursor cursor;
	unsigned int group_index, dbci;
	int screen_candidate_index;
	const struct rotation *rotation;
	struct ballot_contents *ballot;

	cursor = get_cursor_position();
	group_index = cursor.group_index;
	screen_candidate_index = cursor.screen_candidate_index;
	/* If screen candidate index is -1 then cursor is on a group heading */
	if (screen_candidate_index > -1) {
		ballot = get_ballot_contents();
		rotation = get_current_rotation();
		/* SIPL 2011-06-28 Use updated translate function. */
		dbci = translate_group_sci_to_dbci
			(group_index,
			 screen_candidate_index,
			 rotation);
		insert_preference_digit(group_index, dbci, pref);
		/* Redraw the candidates preference box with the new 
		   preference number */
		draw_group_entry(cursor, YES, NO);
	}
}
