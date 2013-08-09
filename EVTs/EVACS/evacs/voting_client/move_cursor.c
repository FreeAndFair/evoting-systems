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
#include "move_cursor.h"
#include "input.h"
#include "voting_client.h"
#include "draw_group_entry.h"

/* Set the default cursor position */
struct cursor current_cursor = {-1,0};

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

	return bc->num_candidates[group_index];
}

/* DDS3.2.12: Update Cursor Position */
static void update_ccp(struct cursor cursor, enum input_event next)
{
	struct cursor new_cursor;
	unsigned int number_of_groups, group_index, number_of_candidates;
	int candidate_index;

	group_index = cursor.group_index;
	candidate_index = cursor.screen_candidate_index;

	number_of_groups = get_num_gps_electorate();
	number_of_candidates = get_num_cands_in_gp(group_index);

	if (next == INPUT_UP) {
		candidate_index -= 1;
		if (candidate_index < 0) {
			candidate_index = number_of_candidates - 1;
		}
	}
	if (next == INPUT_DOWN) {
		candidate_index += 1;
		if (candidate_index == number_of_candidates) {
			candidate_index = 0;
		}
	}
	if (next == INPUT_NEXT) {
		group_index += 1;
		candidate_index = -1;
		if (group_index == number_of_groups) {
			group_index = 0;
		}
	}	
	if (next == INPUT_PREVIOUS) {
		if (group_index == 0) {
			group_index = number_of_groups;
		}
		group_index -= 1;
		candidate_index = -1;
	}
	
	new_cursor.group_index = group_index;
	new_cursor.screen_candidate_index = candidate_index;

	set_cursor_position(new_cursor);

	/* Interrupt any currently playing audio */
	draw_group_entry(new_cursor, YES, true);
}


/* DDS3.2.12: Move Cursor */
void move_cursor(enum input_event next)
{
	struct cursor cursor;

	if ((next == INPUT_UP) || (next == INPUT_DOWN) || (next == INPUT_NEXT)
	    || (next == INPUT_PREVIOUS)) {
		
		/* Unhighlight old screen location */
		cursor = get_cursor_position();
		draw_group_entry(cursor, NO, false);
		
		/* Highlight new screen location */
		update_ccp(cursor, next);
	}
}


