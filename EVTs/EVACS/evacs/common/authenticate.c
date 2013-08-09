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
#include <assert.h>
#include <stdlib.h>
#include "authenticate.h"
#include "voting_errors.h"
#include "http.h"
#include "ballot_contents.h"

/* SIPL 2011-06-21 Modified to support split groups. */
/* Convert the ballot contents from the http variables */
static enum error unpack_ballot_contents(const struct http_vars *vars)
{
	const char *val;
	int i;
	struct ballot_contents *bc;
	/* Number of split HTTP variables. */
	unsigned int num_splits;
	/* Data extracted from one split HTTP variable. */
	unsigned int split_party_index, split_candidate_count;
	/* The previous value of the first of the above. */
	unsigned int last_split_party_index;
	unsigned int split_candidate_count_remaining;

	/* Server response must contain num_groups, and groupXX entries */
	val = http_string(vars, "num_groups");
	if (!val || (i = atoi(val)) <= 0)
		return ERR_SERVER_RESPONSE_BAD;

	/* SIPL 2011-06-21 No longer need to know the number of groups
	   to allocate space for bc. See the comments in ballot_contents.h. */
	bc = malloc(sizeof(*bc));
	if (!bc)
		return ERR_INTERNAL;

	bc->num_groups = i;

	/* SIPL 2011-06-21 Add support for split groups. */

	bc->num_candidates = malloc(i*sizeof(unsigned int));
	if (!bc->num_candidates) {
		free(bc);
		return ERR_INTERNAL;
	}

	/* Allocate space for map.  Note that the length is i+1, not i.
	   The last entry in the map is a dummy entry that points to
	   the location after the end of the
	   num_candidates_in_physical_column array.
	   For example, if there are 5 groups,
	   and 8 physical columns,
	   map_group_to_physical_column[5] == 8.
	   See the comments in ballot_contents.h.
	 */
	bc->map_group_to_physical_column = malloc((i+1)*sizeof(unsigned int));
	if (!bc->map_group_to_physical_column) {
		free(bc->num_candidates);
		free(bc);
		return ERR_INTERNAL;
	}

	/* Extract number of candidates for each group */
	for (i = 0; i < bc->num_groups; i++) {
		char name[sizeof("group") + INT_CHARS];

		sprintf(name, "group%u", (unsigned int)i);
		val = http_string(vars, name);
		if (!val)
			return ERR_SERVER_RESPONSE_BAD;
		bc->num_candidates[i] = atoi(val);
		assert(bc->num_candidates[i] > 0);
	}

	/* SIPL 2011-06-21 Add support for split groups. */
	/* First, determine if any groups are split. */
	val = http_string(vars, "num_splits");
	if (!val) {
	    num_splits = 0;
	} else {
	    num_splits = atoi(val);
	}

	/* The split data returned from the voting server does not
	   indicate the number of candidates in the last physical
	   column of each group.  Therefore, the total number of
	   physical columns in the ballot can be calculated using the
	   following simple formula.
	 */
	bc->num_physical_columns = bc->num_groups + num_splits;

	bc->num_candidates_in_physical_column =
	    malloc(bc->num_physical_columns*sizeof(unsigned int));
	if (!bc->num_candidates_in_physical_column) {
	    free(bc->map_group_to_physical_column);
	    free(bc->num_candidates);
	    free(bc);
	    return ERR_INTERNAL;
	}

	/* SIPL 2011-07-11 Allocate space for map of physical columns
	   to grid blocks.  Allow one extra space in the array, that
	   will map to the very end of the entire ballot.  Nota bene:
	   This map is not filled in here, but must be filled in
	   later before use.  This is done in main_screen.c.
	*/
	bc->map_physical_column_to_grid_block =
	    malloc((bc->num_physical_columns + 1)*sizeof(unsigned int));
	if (!bc->map_physical_column_to_grid_block) {
	    free(bc->num_candidates_in_physical_column);
	    free(bc->map_group_to_physical_column);
	    free(bc->num_candidates);
	    free(bc);
	    return ERR_INTERNAL;
	}

	if (num_splits == 0) {
	    /* No group has been split, so copy the group size
	       data across. */
	    for (i = 0; i < bc->num_groups; i++) {
		bc->map_group_to_physical_column[i] = i;
		bc->num_candidates_in_physical_column[i] =
		    bc->num_candidates[i];
	    }
	} else {
	    /* Extract details of split groups and fill in the
	       arrays accordingly. */

	    /* Iterator over "splitX" HTTP variables. */
	    unsigned int split_index = 0;
	    /* Iterator over num_candidates_in_physical_column[]. */
	    unsigned int physical_column_index = 0;
	    /* Iterator over num_candidates[]. */
	    unsigned int group_index = 0;

	    /* Get first split. */
	    val = http_string(vars, "split0");
	    sscanf(val,"%u,%u",
		   &split_party_index, &split_candidate_count);
	    split_candidate_count_remaining =
		bc->num_candidates[split_party_index];

	    while (physical_column_index < bc->num_physical_columns) {
		char name[sizeof("split") + INT_CHARS];

		/* Copy data until the next split group. */
		while (group_index < split_party_index) {
		    bc->map_group_to_physical_column[group_index] =
			physical_column_index;
		    bc->num_candidates_in_physical_column[
				physical_column_index] =
			bc->num_candidates[group_index];
		    group_index++;
		    physical_column_index++;
		}

		/* Is there a split group to process? */
		if (split_party_index < bc->num_groups) {
		    bc->map_group_to_physical_column[group_index] =
			physical_column_index;
		    do {
			/* This loop fills in all but the last of the physical
			   columns for this split group. */
			bc->num_candidates_in_physical_column[
				physical_column_index] =
			    split_candidate_count;
			split_candidate_count_remaining =
			    split_candidate_count_remaining -
			    split_candidate_count;
			physical_column_index++;

			/* Get next split data. */

			last_split_party_index = split_party_index;

			split_index++;
			if (split_index < num_splits) {
			    sprintf(name, "split%u", split_index);
			    val = http_string(vars, name);
			    sscanf(val,"%u,%u",
				   &split_party_index,
				   &split_candidate_count);
			}
		    } while ((split_index < num_splits) &&
			     (split_party_index == last_split_party_index));
		    /* Fill in the remaining physical column
		       for this split group. */
		    bc->num_candidates_in_physical_column[
				physical_column_index] =
			split_candidate_count_remaining;
		    physical_column_index++;
		    group_index++;
		    if (split_party_index != last_split_party_index)
			    /* New group to be split; reset count of
			       remaining candidates. */
			    split_candidate_count_remaining =
				    bc->num_candidates[split_party_index];

		    /* If no more split data, set split_party_index
		       so that the first inner loop will
		       go round to complete
		       filling in the arrays. */
		    if (split_index == num_splits)
			split_party_index = bc->num_groups;
		}
	    }
	}

	/* Fill in the dummy entry at the end. */
	bc->map_group_to_physical_column[bc->num_groups] =
		bc->num_physical_columns;

	/* ballot contents must be set only once from each authenticate 
	   invocation  */
	assert(!get_ballot_contents());
	set_ballot_contents(bc);
	return ERR_OK;
}

/* DDS3.2.4: Authenticate */
/* Authenticate barcode: returns electorate (to be freed by caller),
   or calls display_error() itself */
enum error authenticate(const struct barcode *bc, struct electorate **elecp)
{
	struct http_vars *reply;
	enum error ret;
	const char *val;
	const struct http_vars request[]
		= { { (char *)"barcode", (char *)bc->ascii }, { NULL, NULL } };

	fprintf(stderr,"common/authenticate: HTTP exchange with %s:%u\n",get_server(), get_port());
	reply = http_exchange(get_server(), get_port(),
			      AUTHENTICATE_CGI, request);
	/* Some error occurred? */
	if (http_error(reply) != ERR_OK)
		return http_error(reply);

	fprintf(stderr,"common/authenticate: HTTP exchange complete\n");
	/* We should have an electorate name, electorate code, and
	   number of seats. */
	val = http_string(reply, "electorate_name");
	if (!val)
		return ERR_SERVER_RESPONSE_BAD;

	/* Now we have the name, we can allocate space for the electorate */
	*elecp = malloc(sizeof(struct electorate) + strlen(val)+1);
	if (!*elecp) return ERR_INTERNAL;
	strcpy((*elecp)->name, val);

	val = http_string(reply, "electorate_code");
	if (!val)
		return ERR_SERVER_RESPONSE_BAD;
	(*elecp)->code = atoi(val);

	val = http_string(reply, "electorate_seats");
	if (!val)
		return ERR_SERVER_RESPONSE_BAD;
	(*elecp)->num_seats = atoi(val);

	/* We also set the ballot contents from these variables */
	ret = unpack_ballot_contents(reply);
	http_free(reply);
	return ret;
}


