#ifndef _DRAW_GROUP_ENTRY_H
#define _DRAW_GROUP_ENTRY_H
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
#include <common/cursor.h>
struct electorate;

enum HlFlag
{
	NO,
	YES
};

/* Draw Group Entry: if highlighted, audio will be played.  If
   interrupt is true, the current audio will be interrupted. */
extern void draw_group_entry(struct cursor cursor,
			     enum HlFlag highlight,
			     bool interrupt);

/* SIPL 2011-06-29 Because there can now be split groups,
   need to be able to draw blank entries in the "middle"
   of a group.  This version of the function is no longer able to cope. */
/* Draw a blank entry */
/* extern void draw_blank_entry(unsigned int group_index, int screen_index);
 */

/* SIPL 2011-06-29 Modification of draw_blank_entry that
   takes a grid block as the first parameter. */
/* Draw a blank entry */
extern void draw_blank_entry_grid_block(unsigned int grid_block,
					int screen_index);

/* SIPL 2011-06-29 As per draw_blank_entry_grid_block() but
   using the completely blank image, without the dividing line at
   the right-hand side. */
extern void draw_blank_entry_no_divider_grid_block(
				unsigned int grid_block,
				int screen_index);

/* Draw a blank group entry */
extern void draw_blank_group_entry(unsigned int group_index);

/* SIPL 2011-06-29 New function taking a grid block as parameter. */
/* Draw a blank group entry */
extern void draw_blank_group_entry_grid_block(unsigned int grid_block);

/* SIPL 2011-07-11 Renamed this function, and made it available. */
/* Calculate how many grid blocks fit across the screen */
extern unsigned int get_grid_blocks_across(
				const struct electorate *voter_elec);

/* SIPL 2011-07-12 Renamed. */
/* How many grid blocks *could* fit on the screen? */
extern unsigned int grid_blocks_possible(void);

#endif /*_DRAW_GROUP_ENTRY_H*/
