#ifndef _VOTE_IN_PROGRESS_H
#define _VOTE_IN_PROGRESS_H
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

/* This file encapsulates everything to do with the voter's current
   preferences */
#include <stdbool.h>
#include <common/evacs.h>
#include "message.h"

/* remove the preference at pref_index: called by deo_delete_preference */
extern void remove_pref(unsigned int pref_index);

/* Remove the last preference: return false if there wasn't one */
extern bool remove_last_pref(struct preference *undone_pref);

/* Add a candidate to the VIP (next preference number) */
extern void add_candidate(unsigned int group_index,
			  unsigned int db_candidate_index);

void change_candidate_prefnum(unsigned int candidate_number, 
			      unsigned int new_pref);

/* Add a candidate with a specific preference number to the VIP */
/* Note that preference numbers start at 1 */
extern void add_candidate_with_pref(unsigned int group_index,
				    unsigned int db_candidate_index,
				    unsigned int prefnum);

/* Get a copy of the vote in progress */
extern const struct preference_set *get_vote_in_progress(void);

/* Delete the current vote */
extern void delete_prefs(void);
#endif /*_VOTE_IN_PROGRESS_H*/
