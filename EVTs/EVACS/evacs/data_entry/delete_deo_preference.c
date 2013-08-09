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
#include <common/cursor.h>
#include <common/database.h>
#include <common/ballot_contents.h>
#include <common/get_electorate_ballot_contents.h>
#include <voting_client/get_rotation.h>
#include <voting_client/main_screen.h>
#include <voting_client/draw_group_entry.h>
#include <voting_client/vote_in_progress.h>
#include "move_deo_cursor.h"
#include "delete_deo_preference.h"

/* DDS3.20: Delete Preference */
static void delete_preference(unsigned int group_index, unsigned int dbci)
{
	const struct preference_set *vip;
	unsigned int i;

	vip = get_vote_in_progress();
	for (i=0; i < vip->num_preferences; i++) {
		if ((vip->candidates[i].group_index == group_index)
		    && (vip->candidates[i].db_candidate_index == dbci)) {
/* shift preferences back one and delete empty pref  */
			remove_pref(i);
		}
		
	}
}
	


/* DDS3.20: Delete DEO Preference */
void delete_deo_preference(void)
{
	struct cursor cursor;
	unsigned int group_index, dbci;
	int candidate_index;
	struct ballot_contents *ballot;
	const struct rotation *rotation;

	cursor = get_cursor_position();
	group_index = cursor.group_index;
	candidate_index = cursor.screen_candidate_index;

	if (candidate_index > -1) {
		ballot = get_ballot_contents();
		rotation = get_current_rotation();
		/* SIPL 2011-06-28 Use updated translate function. */
		dbci = translate_group_sci_to_dbci
			(cursor.group_index,
			 candidate_index, rotation);
		delete_preference(group_index, dbci);
		draw_group_entry(cursor, YES, NO);
	}
}
