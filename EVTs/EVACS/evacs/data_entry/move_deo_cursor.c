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

/*#include <voting_client/move_cursor.h>*/
#include <common/get_electorate_ballot_contents.h>
#include <common/voter_electorate.h>
#include <common/database.h>
#include <voting_client/main_screen.h>
#include <voting_client/draw_group_entry.h>
#include "interpret_deo_keystroke.h"

#include "move_deo_cursor.h"

/* Set the default cursor position */
static struct cursor current_cursor = {DEFAULT_DEO_CURSOR_X,
				       DEFAULT_DEO_CURSOR_Y};

/* DDS3.2.12: Get Cursor Position */
struct cursor get_cursor_position(void)
{
	return current_cursor;
}

/* DDS3.2.12: Set Cursor Position */
void set_cursor_position(struct cursor cursor_position)
{
	current_cursor.group_index = cursor_position.group_index;
	current_cursor.screen_candidate_index 
		= cursor_position.screen_candidate_index;
}

void reset_deo_cursor(void)
{
	current_cursor.group_index = DEFAULT_DEO_CURSOR_X ;
	current_cursor.screen_candidate_index 
		= DEFAULT_DEO_CURSOR_Y;
	
}

/* DDS3.2.12: Get Number of Groups in Electorate */
static unsigned int get_num_gps_electorate(void)
{
	struct ballot_contents *bc;

	/* ballot_contents only contains details of current electorate */
	bc = get_ballot_contents();
	
	return bc->num_groups;
}
	
/* DDS3.2.12: Get Number of Candidates in Group */
static unsigned int get_num_cands_in_gp(unsigned int group_index)
{
	struct ballot_contents *bc;

	bc = get_ballot_contents();
	
	return (unsigned int) bc->num_candidates[group_index];
}


/* DDS3.16: Update DEO Cursor Position */
void update_deo_cursor_position(struct cursor cursor, enum deo_keystroke key)
{
	struct cursor new_cursor;
	unsigned int number_of_groups, group_index, number_of_candidates;
	int candidate_index;

	group_index = cursor.group_index;
	candidate_index = cursor.screen_candidate_index;

	number_of_groups = get_num_gps_electorate();
	number_of_candidates = get_num_cands_in_gp(group_index);

	if (key == DEO_KEYSTROKE_UP) {
		candidate_index -= 1;
		if (candidate_index < 0) {
			candidate_index = number_of_candidates - 1;
		}
	}
	else if (key == DEO_KEYSTROKE_DOWN) {
		candidate_index += 1;
		if (candidate_index == number_of_candidates) {
			candidate_index = 0;
		}
	}
	else if (key == DEO_KEYSTROKE_NEXT) {
		group_index += 1;
		candidate_index = 0;
		if (group_index == number_of_groups) {
			group_index = 0;
		}
	}

	new_cursor.group_index = group_index;
	new_cursor.screen_candidate_index = candidate_index;

	set_cursor_position(new_cursor);

	draw_group_entry(new_cursor, YES, NO);
}

/* DDS3.16: Move DEO Cursor */
void move_deo_cursor(enum deo_keystroke key)
{
	struct cursor cursor;

	if ((key == DEO_KEYSTROKE_DOWN) || (key == DEO_KEYSTROKE_UP) 
	    || (key == DEO_KEYSTROKE_NEXT)) {
		
		/* Unhighlight old screen location */
		cursor = get_cursor_position();
		draw_group_entry(cursor, NO, NO);

		/* Highlight new screen location */
		update_deo_cursor_position(cursor, key);
	}
}
