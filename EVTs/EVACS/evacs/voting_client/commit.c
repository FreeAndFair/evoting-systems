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
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <common/evacs.h>
#include <common/http.h>
#include <common/rotation.h>
#include "get_rotation.h"
#include "get_cursor.h"
#include "message.h"
#include "voting_client.h"
#include "keystroke.h"
#include "commit.h"
#include "vote_in_progress.h"

/* Turn Vote in Progress into a string.  Caller must free result */
static char *build_vote(const struct preference_set *prefs)
{
	char *result;
	unsigned int i;
	/* Comma-separated group-index, db-cand-index pairs */

	result = malloc((INT_CHARS*2 + 2)*prefs->num_preferences + 1);
	if (!result)
		display_error(ERR_INTERNAL);
	result[0] = '\0';

	for (i = 0; i < prefs->num_preferences; i++) {
		/* Add a comma if there was a previous preference */
		if (i != 0) strcat(result, ",");
		/* Append the group and candidate index voted for */
		sprintf(result + strlen(result), "%u,%u",
			prefs->candidates[i].group_index,
			prefs->candidates[i].db_candidate_index);
		assert(prefs->candidates[i].prefnum == i+1);
	}

	return result;
}

/* Encode the rotation in http vars, and NULL terminate them */
static void encode_rotation(struct http_vars *vars, const struct rotation *rot)
{
	unsigned int i;

	for (i = 0; i < rot->size; i++) {
		vars[i].name = malloc(sizeof("rotation") + INT_CHARS);
		vars[i].value = malloc(INT_CHARS + 1);
		if (!vars[i].name || !vars[i].value)
			display_error(ERR_INTERNAL);
		sprintf(vars[i].name, "rotation%u", i);
		sprintf(vars[i].value, "%u", rot->rotations[i]);
	}
	vars[rot->size].name = vars[rot->size].value = NULL;
}

/* DDS3.2.26: Commit Vote */
void commit_vote(struct barcode *bc)
{
	const struct rotation *rot;
	struct http_vars *hvars, *retvars;

	rot = get_current_rotation();
	/* We send barcode, keystrokes, vote, and the rotation vars. */
	hvars = malloc(sizeof(struct http_vars) * (4 + rot->size + 1));
	if (!hvars)
		display_error(ERR_INTERNAL);
	hvars[0].name = strdup("barcode");
	hvars[0].value = strdup(bc->ascii);
	hvars[1].name = strdup("keystrokes");
	hvars[1].value = strdup(get_keystrokes());
	hvars[2].name = strdup("vote");
	hvars[2].value = build_vote(get_vote_in_progress());
	hvars[3].name = strdup("cursor");
	hvars[3].value = sprintf_malloc("%u", get_current_cursor());
	encode_rotation(hvars+4, get_current_rotation());

	/* Have the server to the commit */
	retvars = http_exchange(SERVER_ADDRESS, SERVER_PORT,
				"/cgi-bin/commit_vote",
				hvars);
	/* Abort if there was an error */
	if (http_error(retvars))
		display_error(http_error(retvars));

	http_free(retvars);
	http_free(hvars);
}

	
