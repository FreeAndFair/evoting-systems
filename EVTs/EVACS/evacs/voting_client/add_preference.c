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
#include <common/ballot_contents.h>
#include <common/voter_electorate.h>
#include <common/cursor.h>
#include <common/authenticate.h>
#include "add_preference.h"
#include "vote_in_progress.h"
#include "verify_barcode.h"
#include "get_rotation.h"
#include "move_cursor.h"
#include "draw_group_entry.h"

/* DDS3.2.20 Search VIP for Candidate */
static bool search_vip(unsigned int group_index, int dbci)
{
	const struct preference_set *vip;
	unsigned int i;

	vip = get_vote_in_progress();

	for (i = 0; i < vip->num_preferences; i++) {
		if ((vip->candidates[i].group_index == group_index) 
		    && (vip->candidates[i].db_candidate_index == dbci)) {
			return true;
		}
	}
	return false;
}
			
/* DDS3.2.20: Add Preference */	
void add_preference(void)
{
	struct cursor cursor;
	/* SIPL 2011-06-28 No longer needed because of new translate
	   function.
	const struct ballot_contents *ballot;
	unsigned int num_candidates; */
	unsigned int dbci;
	const struct rotation *rotation;
	bool candidate_found;

	rotation = get_current_rotation();

	cursor = get_cursor_position();
	
	/* If cursor is on a group heading, then ignore selection */
	if (cursor.screen_candidate_index >= 0) {
	/* SIPL 2011-06-28 No longer needed because of new translate
	   function.
		ballot = get_ballot_contents();
	
		num_candidates = ballot->num_candidates[cursor.group_index];
	*/
		
		/* SIPL 2011-06-28 Use updated translate function. */
		dbci = translate_group_sci_to_dbci(cursor.group_index,
				     cursor.screen_candidate_index, 
				     rotation);
		/* Check if this candidate has already been added to the 
		   Vote in Progress */
		candidate_found = search_vip(cursor.group_index, dbci);
		
		if (!candidate_found) {
			add_candidate(cursor.group_index, dbci);
			/* Interrupt audio */
			draw_group_entry(cursor, YES, true);
		}
	}
}
