#ifndef _CURSOR_H
#define _CURSOR_H
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
#include <common/ballot_contents.h>
#include <common/rotation.h>

/* This is what a main-screen cursor looks like */
struct cursor
{
	/* -1 means group heading */
	/* SIPL 2011-06-28 Add support for split groups.
	   screen_candidate_index is a "group_screen_candidate_index",
	   i.e., it ranges from 0 to the number of candidates in
	   the group.  And, as per the previous comment, -1 still
	   means the group heading.
	 */
	int screen_candidate_index;
	unsigned int group_index;
};

/* Translate the cursor's SCREEN candidate index (which is rotated by
   the robson rotation) to the candidate's canonical DATABASE candidate
   index, and vice versa. */
/* SIPL 2011-06-28 Support split groups.  Comment out the
   previous implementations of these functions, making them
   not available, so that there is no chance that they will
   be used elsewhere in the system. */
/*
extern unsigned int translate_dbci_to_sci(unsigned int num_candidates,
					  unsigned int db_candidate_index,
					  const struct rotation *rot);

extern unsigned int translate_sci_to_dbci(unsigned int num_candidates,
					  unsigned int screen_candidate_index,
					  const struct rotation *rot);

extern unsigned int dummy_dbci_to_sci(unsigned int num_candidates,
					  unsigned int db_candidate_index,
					  const struct rotation *rot);

extern unsigned int dummy_sci_to_dbci(unsigned int num_candidates,
					  unsigned int screen_candidate_index,
					  const struct rotation *rot);
*/

/* SIPL 2011-06-28 New implementations of these key functions. */

extern unsigned int translate_group_dbci_to_sci(unsigned int group_index,
					  unsigned int db_candidate_index,
					  const struct rotation *rot);

extern unsigned int translate_group_sci_to_dbci(unsigned int group_index,
					  unsigned int screen_candidate_index,
					  const struct rotation *rot);

#endif /*_CURSOR_H*/
