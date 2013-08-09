#ifndef _BALLOT_CONTENTS_H
#define _BALLOT_CONTENTS_H 

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

/* this file contains the prototype accessors for ballot contents   */


/* This is as much of the ballot contents as we need to know (this
   electorate only) */
struct ballot_contents
{
	/* Total number of groups */
	unsigned int num_groups;

	/* Number of candidates in each group */
	/* An array indexed by group number - 1 (ie. zero-based) */
	/* SIPL 2011-06-21 This was declared int num_candidates[0] and
	  space was allocated directly within the struct for an array of the
	  appropriate size.
	  Changed to a pointer; now space must be allocated separately. */
	unsigned int *num_candidates;

	/* Total number of physical columns.  If no
	   groups are split, this equals num_groups. */
	unsigned int num_physical_columns;

	/* Mapping of group to "physical column".  For example,
	   suppose group 0 occupies two physical columns.  Then
	   map_group_to_physical_column[0] == 0 and
	   map_group_to_physical_column[1] == 2.
	   There is an additional dummy entry at the end for
	   convenience.  For example, if there are 5 groups,
	   and 8 physical columns,
	   map_group_to_physical_column[5] == 8.
	   This dummy value is used in voting_client/main_screen.c
	   and voting_client_stripped/main_screen.c.
	*/
	unsigned int *map_group_to_physical_column;

	/* Number of candidates in each physical column.  If no
	   groups are split, this is an identical copy of
	   num_candidates[]. */
	unsigned int *num_candidates_in_physical_column;

	/* Mapping of "physical column" to "grid block".  The ballot
	   is laid out as a grid, and the elements of that grid are
	   "grid blocks", numbered sequentially from 0.  For example,
	   if there are five grid blocks per row, the first grid block
	   in the second row is numbered 5.  The physical columns are
	   assigned to grid blocks starting at the top left of the
	   screen, working left to right, top to bottom.  In case a
	   multi-column group does not fit at the end of a row, it is
	   moved in its entirety to the next row, leaving a gap at the
	   end of the row.  For example, suppose there are five grid
	   blocks per row, and the first row contains four one-column
	   groups followed by a two-column group.  Then:
	   map_physical_column_to_grid_block[0]=0
	   map_physical_column_to_grid_block[1]=1
	   map_physical_column_to_grid_block[2]=2
	   map_physical_column_to_grid_block[3]=3
	   map_physical_column_to_grid_block[4]=5
	   map_physical_column_to_grid_block[5]=6
	   As per map_group_to_physical_column, there is an additional dummy
	   entry at the end for convenience.  For example, if there are
	   8 physical columns and 10 grid blocks in the entire grid
	   (e.g. two rows of five grid blocks),
	   map_physical_column_to_grid_block[8] == 10.
	   This array is filled in by main_screen.c, and its values
	   are used in draw_group_entry.c.
	*/
	unsigned int *map_physical_column_to_grid_block;

};

/* Return the ballot contents */
extern struct ballot_contents *get_ballot_contents(void);

/* Set the ballot contents (called from authenticate) */
extern void set_ballot_contents(struct ballot_contents *bc);

#endif /* _BALLOT_CONTENTS_H  */
