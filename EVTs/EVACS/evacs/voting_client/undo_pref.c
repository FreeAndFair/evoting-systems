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
#include <common/authenticate.h>
#include <common/cursor.h>
/* SIPL 2011-06-28 No longer needed because of new translate
   function.
   #include <common/ballot_contents.h> */
#include "undo_pref.h"
#include "move_cursor.h"
#include "vote_in_progress.h"
#include "get_rotation.h"
#include "draw_group_entry.h"
#include "audio.h"

/* DDS3.2.18: Unhighlight Current Candidate */
static void unhighlight_cand(void)
{
	unsigned int prefnum;
	struct cursor last_pref, current_cursor;
	const struct preference_set *vip;
	int sci;
	/* SIPL 2011-06-28 No longer needed because of new translate
	   function.
	   unsigned int num_candidates;
	   struct ballot_contents *ballot; */
	
	vip = get_vote_in_progress();
	prefnum = vip->num_preferences;
	
	last_pref.group_index = vip->candidates[prefnum].group_index;

	/* need to get the screen candidate index corresponding to the db 
	   candidate index in the vote in progress */
	/* SIPL 2011-06-28 No longer needed because of new translate
	   function.
	ballot = get_ballot_contents();
	num_candidates = ballot->num_candidates[last_pref.group_index];
	*/

	/* SIPL 2011-06-28 Use updated translate function. */
	sci = translate_group_dbci_to_sci(last_pref.group_index,
				    vip->candidates[prefnum]
				    .db_candidate_index,
				    get_current_rotation());
						       
	last_pref.screen_candidate_index = sci;
	
	/* Redraw the prefbox and candidate name unhighlighted and 
	   without a prefnum */
	draw_group_entry(last_pref, NO, false);

	/* If cursor was moved after last preference, unhighlight the 
	   current cursor position */
	current_cursor = get_cursor_position();
	if ((current_cursor.group_index != last_pref.group_index) 
		|| (current_cursor.screen_candidate_index 
		    != last_pref.screen_candidate_index)) {
		draw_group_entry(current_cursor, NO, false);
	}
}

/* DDS3.2.18: Move Cursor to Candidate */
static void move_cursor_to_cand(unsigned int group_index, 
				unsigned int db_candidate_index)
{
	struct cursor cursor;
	int screen_candidate_index;
	const struct rotation *rot;
	/* SIPL 2011-06-28 No longer needed because of new translate
	   function.
	   struct ballot_contents *ballot;
	   unsigned int num_candidates;
	   ballot = get_ballot_contents(); */

	/* SIPL 2011-06-28 No longer needed because of new translate
	   function.
	   num_candidates = ballot->num_candidates[group_index]; */

	rot = get_current_rotation();

	/* SIPL 2011-06-28 Use updated translate function. */
	screen_candidate_index = translate_group_dbci_to_sci(group_index, 
						       db_candidate_index, 
						       rot);
	
	cursor.screen_candidate_index = screen_candidate_index;
	cursor.group_index = group_index;
	
	/* Highlight the new cursor position: do not interrupt audio. */
	draw_group_entry(cursor, YES, false);
	
	set_cursor_position(cursor);
}

/* DDS3.2.18: Undo Preference */
void undo_pref(void)
{
	bool UndoOK;
	unsigned int prefnum;
	const struct preference_set *vip;
	struct preference undone_pref;

	UndoOK = remove_last_pref(&undone_pref);

	if (UndoOK) {
		vip = get_vote_in_progress();
		prefnum = vip->num_preferences;
	
		/* Unhighlight the current cursor position and clear last 
		   preference number */ 
		unhighlight_cand();

		play_audio(true, get_audio("undo.raw"));

		/* Move the cursor to the undone preference position and 
		   highlight */
		move_cursor_to_cand(undone_pref.group_index,
				    undone_pref.db_candidate_index);
	}
}
