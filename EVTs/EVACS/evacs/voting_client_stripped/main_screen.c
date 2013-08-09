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
#include <common/ballot_contents.h>
#include <common/voter_electorate.h>
#include <common/authenticate.h>
#include "voting_client.h"
#include "message.h"
#include "initiate_session.h"
#include "draw_group_entry.h"
#include "main_screen.h"

void display_screen(const struct electorate *electorate, const struct ballot_contents *bc);

/* SIPL 2011-06-29 Modified to support split groups, as per
   the "real" voting client.  But this code is not called. */
/* DDS3.2.8: Display Main Voting Screen */
/* DDS3.12: Display DEO Ballot Screen */
void dsp_mn_vt_scn(void)
{
	const struct electorate *electorate;
	struct ballot_contents *bc;
	unsigned int group_index;
	unsigned int physical_column;
	unsigned int grid_block;
	int cand;
	struct cursor cursor_position;
	struct image *ballot_h_image;

	/* Number of grid blocks in each row. */
	unsigned int groups_across;

	/* grid_block_mod_groups_across = (grid_block % groups_across) */
	unsigned int grid_block_mod_groups_across;
	/* The first grid block of the next group (or the end
	   of the ballot, if there is no next group). */
	unsigned int next_grid_block;

	electorate = get_voter_electorate();
	bc = get_ballot_contents();
	ballot_h_image = get_bh_image(get_language(), electorate);
	paste_image(0,0,ballot_h_image);

	/* SIPL 2011-07-11 Need this to fill in
	   map_physical_column_to_grid_block. */
	groups_across = get_grid_blocks_across(electorate);

	/* SIPL 2011-06-29 Now loop over physical columns and grid blocks
	   as well as groups. Fill in map_physical_column_to_grid_block
	   during this process. */
	group_index = 0;
	physical_column = 0;
	grid_block = 0;
	while (group_index < bc->num_groups) {
		/* Need to fill in all the map entries for the group
		   before calling draw_group_entry. */
		bc->map_physical_column_to_grid_block[physical_column] =
			grid_block;
		/* For the rest in the group, draw blank entry */
		/* All physical columns but the last for this group. */
		while (physical_column <
		       bc->map_group_to_physical_column[group_index+1] - 1) {
			for (cand = bc->num_candidates_in_physical_column[
				physical_column];
			     cand < electorate->num_seats; cand++)
				draw_blank_entry_no_divider_grid_block(
					grid_block, cand);
			physical_column++;
			grid_block++;
			bc->map_physical_column_to_grid_block[
					physical_column] = grid_block;
		}
		/* The last physical column for this group. */
		for (cand = bc->num_candidates_in_physical_column[
				physical_column];
		     cand < electorate->num_seats; cand++)
			draw_blank_entry_grid_block(grid_block, cand);

		/* Now all of the entries in
		   map_physical_column_to_grid_block required for
		   this group have been filled in, so the candidates
		   can be drawn. */
		/* candidate -1 corresponds to group heading */
		for (cand = -1;
		     cand < (int)bc->num_candidates[group_index];
		     cand++) {
			cursor_position.group_index = group_index;
			cursor_position.screen_candidate_index = cand;
			draw_group_entry(cursor_position,NO,false);
		}

		group_index++;
		physical_column++;
		grid_block++;

		/* Is there a next group, and, if so, it there room for
		   the next group?
		   If this is the last group, set the map value to
		   the grid block after the end of the entire screen.
		   Otherwise, set the map value to the grid block
		   at the beginning of the next row.
		   Group group_index occupies
		   (bc->map_group_to_physical_column[group_index+1] -
		   bc->map_group_to_physical_column[group_index])
		   physical columns. */
		grid_block_mod_groups_across = grid_block % groups_across;
		if (group_index < bc->num_groups) {
			if (grid_block_mod_groups_across +
			    (bc->map_group_to_physical_column[group_index+1] -
			     bc->map_group_to_physical_column[group_index])
			    > groups_across)
				/* No room.  Move to the next row. */
				next_grid_block = grid_block + (groups_across -
					grid_block_mod_groups_across);
			else
				/* There is room. */
				next_grid_block = grid_block;
		} else {
			/* This is the last group. */
			next_grid_block = grid_blocks_possible();
		}
		/* Now fill in the map entry. */
		bc->map_physical_column_to_grid_block[physical_column] =
			next_grid_block;

		/* Fill in any blank grid blocks at the end of the row,
		   or the ballot. */
		while (grid_block < next_grid_block) {
			draw_blank_group_entry_grid_block(grid_block);
			for (cand = 0; cand < (int)electorate->num_seats;
			     cand++)
				draw_blank_entry_grid_block(grid_block,
							    cand);
			grid_block++;
		}
	}
}

/* SIPL 2011-06-29 Modified to support split groups. */
void display_screen(const struct electorate *electorate, const struct ballot_contents *bc)
{
	unsigned int group_index;
	unsigned int physical_column;
	unsigned int grid_block;
	int cand;
	struct cursor cursor_position;
	struct image *ballot_h_image;

	/* Number of grid blocks in each row. */
	unsigned int groups_across;

	/* grid_block_mod_groups_across = (grid_block % groups_across) */
	unsigned int grid_block_mod_groups_across;
	/* The first grid block of the next group (or the end
	   of the ballot, if there is no next group). */
	unsigned int next_grid_block;

	ballot_h_image = get_bh_image(get_language(), electorate);
	paste_image(0,0,ballot_h_image);

	/* SIPL 2011-07-11 Need this to fill in
	   map_physical_column_to_grid_block. */
	groups_across = get_grid_blocks_across(electorate);

	/* SIPL 2011-06-29 Now loop over physical columns and grid blocks
	   as well as groups. Fill in map_physical_column_to_grid_block
	   during this process. */
	group_index = 0;
	physical_column = 0;
	grid_block = 0;
	while (group_index < bc->num_groups) {
		/* Need to fill in all the map entries for the group
		   before calling draw_group_entry. */
		bc->map_physical_column_to_grid_block[physical_column] =
			grid_block;
		/* For the rest in the group, draw blank entry */
		/* All physical columns but the last for this group. */
		while (physical_column <
		       bc->map_group_to_physical_column[group_index+1] - 1) {
			for (cand = bc->num_candidates_in_physical_column[
				physical_column];
			     cand < electorate->num_seats; cand++)
				draw_blank_entry_no_divider_grid_block(
					grid_block, cand);
			physical_column++;
			grid_block++;
			bc->map_physical_column_to_grid_block[
					physical_column] = grid_block;
		}
		/* The last physical column for this group. */
		for (cand = bc->num_candidates_in_physical_column[
				physical_column];
		     cand < electorate->num_seats; cand++)
			draw_blank_entry_grid_block(grid_block, cand);

		/* Now all of the entries in
		   map_physical_column_to_grid_block required for
		   this group have been filled in, so the candidates
		   can be drawn. */
		/* candidate -1 corresponds to group heading */
		for (cand = -1;
		     cand < (int)bc->num_candidates[group_index];
		     cand++) {
			cursor_position.group_index = group_index;
			cursor_position.screen_candidate_index = cand;
			draw_group_entry(cursor_position,NO,false);
		}

		group_index++;
		physical_column++;
		grid_block++;

		/* Is there a next group, and, if so, it there room for
		   the next group?
		   If this is the last group, set the map value to
		   the grid block after the end of the entire screen.
		   Otherwise, set the map value to the grid block
		   at the beginning of the next row.
		   Group group_index occupies
		   (bc->map_group_to_physical_column[group_index+1] -
		   bc->map_group_to_physical_column[group_index])
		   physical columns. */
		grid_block_mod_groups_across = grid_block % groups_across;
		if (group_index < bc->num_groups) {
			if (grid_block_mod_groups_across +
			    (bc->map_group_to_physical_column[group_index+1] -
			     bc->map_group_to_physical_column[group_index])
			    > groups_across)
				/* No room.  Move to the next row. */
				next_grid_block = grid_block + (groups_across -
					grid_block_mod_groups_across);
			else
				/* There is room. */
				next_grid_block = grid_block;
		} else {
			/* This is the last group. */
			next_grid_block = grid_blocks_possible();
		}
		/* Now fill in the map entry. */
		bc->map_physical_column_to_grid_block[physical_column] =
			next_grid_block;

		/* Fill in any blank grid blocks at the end of the row,
		   or the ballot. */
		while (grid_block < next_grid_block) {
			draw_blank_group_entry_grid_block(grid_block);
			for (cand = 0; cand < (int)electorate->num_seats;
			     cand++)
				draw_blank_entry_grid_block(grid_block,
							    cand);
			grid_block++;
		}
	}
}
