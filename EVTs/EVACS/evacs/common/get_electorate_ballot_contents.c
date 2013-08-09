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

#include <stdlib.h>
#include <assert.h>
#include "evacs.h"
#include "database.h"
#include "ballot_contents.h"
#include "get_electorate_ballot_contents.h"

/* SIPL 2011-06-27 Support split groups. */
struct ballot_contents *get_electorate_ballot_contents(PGconn *conn,
						       unsigned int electorate_code)
/* fill a ballot_contents structure with database values */
{
	struct ballot_contents *ret;
	PGresult *result;
	unsigned int num_rows,i;

	unsigned int num_splits;

	/* retrieve candidate count for each group from database */

	result = SQL_query(conn,
			   "SELECT p.index, count(c.name) "
			   "FROM party p, candidate c "
			   "WHERE p.electorate_code = %u "
			   "AND c.electorate_code = %u "
			   "AND c.party_index = p.index "
			   "GROUP BY p.index;"
			   ,electorate_code,electorate_code);
	
	num_rows = PQntuples(result);
	if (num_rows == 0) bailout("No candidates returned from DB");
	
	/* SIPL 2011-06-27 No longer need to know the number of groups
	   to allocate space for ret. */
	ret = malloc(sizeof(*ret));
	/* fill in the data structure */
	ret->num_groups = num_rows;

	ret->num_candidates = malloc(num_rows*sizeof(unsigned int));

	/* Allocate space for map.  Note that the length is num_rows+1, not
	   num_rows.
	   The last entry in the map is a dummy entry that points to
	   the location after the end of the
	   num_candidates_in_physical_column array.
	   For example, if there are 5 groups,
	   and 8 physical columns,
	   map_group_to_physical_column[5] == 8.
	 */
	ret->map_group_to_physical_column =
		malloc((num_rows+1)*sizeof(unsigned int));

	/* Fill in num_candidates[]. */
	for (i=0;i<num_rows;i++) {
		/* 2011-06-03
		   The next line was:
		   ret->num_candidates[i] = atoi(PQgetvalue(result, i, 1));
		   This relies on the SELECT statement returning results
		   ordered by p.index.  It seems that this was
		   indeed the case.  But not any longer.
		*/
		ret->num_candidates[atoi(PQgetvalue(result, i, 0))] =
			atoi(PQgetvalue(result, i, 1));
	}
	PQclear(result);

	/* Get split data and fill in remaining fields */
	result = SQL_query(conn,
			   "SELECT party_index,physical_column_index,"
			   "candidate_count FROM column_splits "
			   "WHERE electorate_code = %u "
			   "ORDER BY party_index, physical_column_index;",
			   electorate_code);
	num_splits = PQntuples(result);

	ret->num_physical_columns = ret->num_groups + num_splits;

	ret->num_candidates_in_physical_column =
	    malloc(ret->num_physical_columns*sizeof(unsigned int));

	/* SIPL 2011-07-12 Allocate space for map of physical columns
	   to grid blocks.  Allow one extra space in the array, that
	   will map to the very end of the entire ballot.  Nota bene:
	   This map is not filled in here, but must be filled in
	   later before use.  This is done in main_screen.c.
	*/
	ret->map_physical_column_to_grid_block =
	    malloc((ret->num_physical_columns + 1)*sizeof(unsigned int));

	if (num_splits == 0) {
	    /* No group has been split, so copy the group size
	       data across. */
	    for (i = 0; i < ret->num_groups; i++) {
		ret->map_group_to_physical_column[i] = i;
		ret->num_candidates_in_physical_column[i] =
		    ret->num_candidates[i];
	    }
	} else {
	    /* Extract details of split groups and fill in the
	       arrays accordingly. */

	    /* Iterator over split data from the database. */
	    unsigned int split_index = 0;
	    /* Iterator over num_candidates_in_physical_column[]. */
	    unsigned int physical_column_index = 0;
	    /* Iterator over num_candidates[]. */
	    unsigned int group_index = 0;

	    /* Get first split (row 0 of result). */
	    unsigned int split_party_index = atoi(PQgetvalue(result, 0, 0));
	    unsigned int split_candidate_count = atoi(PQgetvalue(result, 0, 2));
	    unsigned int split_candidate_count_remaining =
		ret->num_candidates[split_party_index];

	    /* Keep track of previous split_party_index to identify
	       the end of the split data for a group. */
	    unsigned int last_split_party_index;

	    while (physical_column_index < ret->num_physical_columns) {

		/* Copy data until we get to the next split group. */
		while (group_index < split_party_index) {
		    ret->map_group_to_physical_column[group_index] =
			physical_column_index;
		    ret->num_candidates_in_physical_column[
				physical_column_index] =
			ret->num_candidates[group_index];
		    group_index++;
		    physical_column_index++;
		}

		/* Is there a split group to process? */
		if (split_party_index < ret->num_groups) {
		    ret->map_group_to_physical_column[group_index] =
			physical_column_index;
		    do {
			/* This loop fills in all but the last of the physical
			   columns for this split group. */
			ret->num_candidates_in_physical_column[
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
			    split_party_index =
				    atoi(PQgetvalue(result, split_index, 0));
			    split_candidate_count =
				    atoi(PQgetvalue(result, split_index, 2));
			}
		    } while ((split_index < num_splits) &&
			     (split_party_index == last_split_party_index));
		    /* Fill in remaining physical column
		       for this split group. */
		    ret->num_candidates_in_physical_column[
				physical_column_index] =
			split_candidate_count_remaining;
		    physical_column_index++;
		    group_index++;
		    if (split_party_index != last_split_party_index)
			    /* New group to be split; reset count of
			       remaining candidates. */
			    split_candidate_count_remaining =
				    ret->num_candidates[split_party_index];

		    /* If no more split data, set split_party_index
		       so that the first inner loop will
		       go round to complete
		       filling in the arrays. */
		    if (split_index == num_splits)
			split_party_index = ret->num_groups;
		}
	    }
	}

	/* Fill in the dummy entry at the end. */
	ret->map_group_to_physical_column[ret->num_groups] =
		ret->num_physical_columns;

	PQclear(result);
	return ret;
}
