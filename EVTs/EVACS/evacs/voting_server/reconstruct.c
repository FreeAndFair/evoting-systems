/* This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd.
   
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

#include <stdbool.h>
#include <assert.h>
#include <stdlib.h>
#include <libpq-fe.h>
#include <common/ballot_contents.h>
#include <common/cursor.h>
#include <common/evacs.h>
#include "commit_vote.h"
#include "reconstruct.h"

/* Number of candidates in a group */
static unsigned int num_candidates(unsigned int group)
{
	struct ballot_contents *bc;

	bc = get_ballot_contents();
	assert(group < bc->num_groups);
	return bc->num_candidates[group];
}

/* Number of groups in electorate */
static unsigned int num_groups(void)
{
	struct ballot_contents *bc;

	bc = get_ballot_contents();
	return bc->num_groups;
}

/* Is this a candidate?  Is it not already selected? */
static bool can_place_in_prefs(const struct preference_set *prefs,
			       struct cursor where,
			       const struct rotation *rot)
{
	unsigned int i;
	unsigned int dbci;

	/* Can't place group headings in preferences */
	if (where.screen_candidate_index == -1)
		return false;

	/* SIPL 2011-06-28 Use updated translate function. */
	dbci = translate_group_sci_to_dbci(where.group_index,
				     where.screen_candidate_index,
				     rot);

	/* Look for this candidate in the preferences */
	for (i = 0; i < prefs->num_preferences; i++)
		if (prefs->candidates[i].group_index == where.group_index
		    && prefs->candidates[i].db_candidate_index == dbci)
			return false;

	/* Not found. */
	return true;
}

/* Append candidate to preferences */
static void place_cand_in_prefs(struct preference_set *prefs,
				struct cursor where,
				const struct rotation *rot)
{
	unsigned int dbci;

	assert(where.screen_candidate_index >= 0);

	/* Who are they on, exactly? */
	/* SIPL 2011-06-28 Use updated translate function. */
	dbci = translate_group_sci_to_dbci(where.group_index,
				     where.screen_candidate_index,
				     rot);

	/* Can never get more than this many preferences */
	assert(prefs->num_preferences < PREFNUM_MAX);

	prefs->candidates[prefs->num_preferences].group_index
		= where.group_index;
	prefs->candidates[prefs->num_preferences].db_candidate_index = dbci;
	prefs->candidates[prefs->num_preferences].prefnum
		= prefs->num_preferences + 1;
	prefs->num_preferences++;
}

static struct cursor remove_cand_from_prefs(struct preference_set *prefs,
					    const struct rotation *rot,
					    struct cursor start)
{
	struct cursor where;

	/* If there are still preferences, move them to last selected
           candidate */
	if (prefs->num_preferences != 0) {
		struct preference *lastcand;

		lastcand = &prefs->candidates[prefs->num_preferences-1];
		where.group_index = lastcand->group_index;
		/* SIPL 2011-06-28 Use updated translate function. */
		where.screen_candidate_index
			= translate_group_dbci_to_sci(where.group_index,
						lastcand->db_candidate_index,
						rot);
		/* Delete last preference */
		prefs->num_preferences--;
		return where;
	} else {
		/* Nothing to undo: don't move cursor */
		return start;
	}
}

/* DDS3.2.26: Reconstruct Keystrokes */
static struct preference_set recon_keystrokes(const struct rotation *rot,
					      const char *keystroke,
					      const int cursor)
{
	struct cursor where;
	unsigned int i;
	struct preference_set prefs;

	/* Start on <cursor> group heading, with no preferences */
	where.group_index = cursor;
	where.screen_candidate_index = -1;
	prefs.num_preferences = 0;

	/* Run through keystrokes until we hit end of string */
	for (i = 0; keystroke[i]; i++) {
		switch (keystroke[i]) {
		case 'U':
			/* UP: Wrap if they are at the top (they can't
                           get back to the title though) */
			if (where.screen_candidate_index <= 0)
				where.screen_candidate_index 
					= num_candidates(where.group_index)-1;
			else
				where.screen_candidate_index--;
			break;

		case 'D':
			/* DOWN: Wrap if they are at the bottom (don't
                           go back to title though) */
			if (where.screen_candidate_index
			    == num_candidates(where.group_index)-1)
				where.screen_candidate_index = 0;
			else
				where.screen_candidate_index++;
			break;

		case 'N':
			/* NEXT: Wrap if they are at the last group */
			if (where.group_index == num_groups()-1)
				where.group_index = 0;
			else
				where.group_index++;
			where.screen_candidate_index = -1;
			break;

		case 'P':
			/* PREVIOUS: Wrap if they are at the first group */
			if (where.group_index == 0)
				where.group_index = num_groups()-1;
			else
				where.group_index--;
			where.screen_candidate_index = -1;
			break;

		case 'S':
			/* SELECT: Select if on candidate, and not already
			   selected */
			if (can_place_in_prefs(&prefs, where, rot))
				place_cand_in_prefs(&prefs, where, rot);
			break;

		case 'X': /* UNDO: move to last selected candidate,
			     and unselect them, or do nothing. */
			where = remove_cand_from_prefs(&prefs, rot, where);
			break;

		default:
			bailout("Invalid keystroke `%c' detected\n",
				keystroke[i]);
		}
	}
	return prefs;
}

/* DDS3.2.26: Compare Votes */
static bool compare_votes(const struct preference_set *recon_vote,
			  const struct preference_set *vote)
{
	unsigned int i;

	if (recon_vote->num_preferences != vote->num_preferences) return false;

	/* "vote" is a comma separated list of group index/db
           candidate index pairs */
	for (i = 0; i < recon_vote->num_preferences; i++) {
		/* Group index and candidate index must match */
		if (recon_vote->candidates[i].group_index
		    != vote->candidates[i].group_index
		    || recon_vote->candidates[i].db_candidate_index
		    != vote->candidates[i].db_candidate_index)
			return false;

		/* Both should have ascending prefnums, starting at 1,
		   so they should always match */
		if (recon_vote->candidates[i].prefnum
		    != vote->candidates[i].prefnum)
			return false;
	}

	/* Nothing mismatched. */
	return true;
}

bool reconstruct_and_compare(const struct rotation *rot,
			     const char *keystrokes,
			     const struct preference_set *vote,
			     const int cursor)
{
	struct preference_set prefs;

	prefs = recon_keystrokes(rot, keystrokes, cursor);

	return compare_votes(&prefs, vote);
}
