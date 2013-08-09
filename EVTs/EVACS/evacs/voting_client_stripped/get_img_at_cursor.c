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

#include <string.h>
#include <stdbool.h>
#include <assert.h>
#include <common/cursor.h>
#include <common/voter_electorate.h>
/* SIPL 2011-06-28 No longer needed because of new translate
   function.
   #include <common/ballot_contents.h> */
#include "get_rotation.h"
#include "get_img_at_cursor.h"
#include "message.h"
#include "voting_client.h"
#include "vote_in_progress.h"

extern struct ballot_contents *get_electorate_info(unsigned int ecode);

static unsigned int get_pref_num(unsigned int group_index,
				 unsigned int dbci)
{
	const struct preference_set *vip;
	unsigned int i;

	vip = get_vote_in_progress();

	/* If not found, the preference number is zero */
	for (i = 0; i < vip->num_preferences; i++) {
		if (vip->candidates[i].group_index == group_index
		    && vip->candidates[i].db_candidate_index == dbci) {
			assert(vip->candidates[i].prefnum != 0);
			return vip->candidates[i].prefnum;
		}
	}
	/* Not found */
	return 0;
}

/* DDS3.2.12: Get Preference Image for Candidate */
static struct image *get_pref_img_for_candidate(const struct electorate *elec,
						unsigned int group_index,
						unsigned int dbci)
{
	unsigned int prefnum;

	prefnum = get_pref_num(group_index, dbci);
	return get_preference_image(elec->code, prefnum);
}

/*
static struct audio *
get_pref_audio_for_candidate(unsigned int group_index,
			     unsigned int dbci)
{
	unsigned int prefnum;

	prefnum = get_pref_num(group_index, dbci);

	if (prefnum != 0)
		return get_audio("numbers/%u.raw", prefnum);
	else
		return NULL;
}
*/

/* DDS3.2.12: Get Image Under Cursor */
struct image_set get_img_at_cursor(const struct cursor *cursor)
{
	struct image_set set = { NULL, NULL, NULL };
	const struct electorate *elec;

	elec = get_voter_electorate();

	/* Are they on the group heading? */
	if (cursor->screen_candidate_index == -1) {
		set.group = get_group_image(elec->code, cursor->group_index);
	} else {
		unsigned int dbci;
		/* SIPL 2011-06-28 No longer needed.
		   struct ballot_contents *ballot; */

		assert(cursor->screen_candidate_index >= 0);
		/* We need to know the number of candidates in this group */
	//	ballot = get_ballot_contents();
		/* SIPL 2011-06-28 No longer needed.
		   ballot = get_electorate_info(elec->code); */

		/* They're on a candidate.  Translate. */
		/* SIPL 2011-06-28 Remove the pretence of using a rotation.
		   The previous code had exactly the same end result.
		*/
		dbci = cursor->screen_candidate_index;

		set.candidate = get_candidate_image(elec->code,
						    cursor->group_index,
						    dbci);
		set.prefnumber
			= get_pref_img_for_candidate(elec,
						     cursor->group_index,
						     dbci);
	}
	return set;
}

	
	
