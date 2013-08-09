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

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <malloc.h>
#include <libpq-fe.h>
#include <common/rotation.h>
#include <common/database.h>
#include <common/ballot_contents.h>
#include "voting_client.h"
#include "message.h"
#include "initiate_session.h"
#include "accumulate_preferences.h"

struct ballot_contents *get_electorate_info(unsigned int ecode);
extern void show_ballot(const struct electorate *electorate, const struct ballot_contents *bc);



/* DDS3.1: Do Voting */
int main(int argc, char *argv[])
{
   struct electorate e ;
   struct ballot_contents *bc ;

	if (argc < 6 || argc > 7)
	{
	  fprintf(stderr, "\nStripped-down voting client used to preview ballot papers\n");
	  fprintf(stderr, "Usage: %s <electorate_name> <electorate_code> <number_of_seats> <screen width> <screen height>\n", argv[0]);
	  fprintf(stderr, "The electorate_code & number_of_seats should be as specified in the electorates.txt file\n");
	  fprintf(stderr, "e.g. %s Brindabella 1 5 1152 864\n", argv[0]);
	  return(-1);
	}
	sprintf(e.name, argv[1]);
	e.code=atoi(argv[2]);
	e.num_seats=atoi(argv[3]);
	bc=get_electorate_info(e.code);
	/* SIPL 2011-06-29 Now must store this, as it is accessed later
	   while drawing the ballot. */
	set_ballot_contents(bc);
	store_electorate(&e);

	/* If we have > 6 arguments, monitor is upside down */
	initialise_display(atoi(argv[4]), atoi(argv[5]), (argc == 7 ));
	init_session();
	show_ballot(&e, bc);
	sleep(60);
	return(0);
}

/* SIPL 2011-06-29 Updated to support split groups. */
struct ballot_contents *get_electorate_info(unsigned int ecode)
{
	PGconn *conn;
        PGresult *result;
	unsigned int num_groups,group;
        struct ballot_contents *bc;

	unsigned int num_splits,i;

	conn = connect_db("evacs");
	if (!conn) 
	{
		fprintf(stderr, "Could not open database connection\n");
		exit(-1);
	}
	
	result = SQL_query(conn,
			   "SELECT party_index,count(index) FROM candidate "
			   "WHERE electorate_code = %u "
			   "GROUP BY party_index;",ecode);

	if ( (num_groups = PQntuples(result)) == 0 )
	{
	  	fprintf(stderr,"No groups found for this electorate.\n");
		exit(-1);
	}

	/* SIPL 2011-06-29 No longer need to know the number of groups
	   to allocate space for bc. */

	bc = malloc(sizeof(*bc));
        if (!bc)  
	{
		fprintf(stderr, "Malloc Failed, System Low on Memory\n");
		exit(-1);
	}

	bc->num_groups=num_groups;
//fprintf(stderr, "setting num_groups to %d\n", bc->num_groups);

	bc->num_candidates = malloc(num_groups*sizeof(unsigned int));

	/* Allocate space for map.  Note that the length is num_groups+1, not
	   num_groups.
	   The last entry in the map is a dummy entry that points to
	   the location after the end of the
	   num_candidates_in_physical_column array.
	   For example, if there are 5 groups,
	   and 8 physical columns,
	   map_group_to_physical_column[5] == 8.
	 */
	bc->map_group_to_physical_column =
		malloc((num_groups+1)*sizeof(unsigned int));

	for (group=0;group<num_groups;group++) {
          /* 2011-05-24 
             The next line was:
             bc->num_candidates[group] = atoi(PQgetvalue(result,group,1));
             This relies on the SELECT statement returning results
             ordered by party_index.  It seems that this was
             indeed the case.  But not any longer.
          */

	  bc->num_candidates[atoi(PQgetvalue(result,group,0))] =
                             atoi(PQgetvalue(result,group,1));
//fprintf(stderr, "setting cand[%u] to %d\n", group, bc->num_candidates[group]);
	}
	PQclear(result);

	/* Get split data and fill in remaining fields */
	result = SQL_query(conn,
			   "SELECT party_index,physical_column_index,"
			   "candidate_count FROM column_splits "
			   "WHERE electorate_code = %u "
			   "ORDER BY party_index, physical_column_index;",
			   ecode);
	num_splits = PQntuples(result);

	bc->num_physical_columns = bc->num_groups + num_splits;

	bc->num_candidates_in_physical_column =
	    malloc(bc->num_physical_columns*sizeof(unsigned int));

	/* SIPL 2011-07-12 Allocate space for map of physical columns
	   to grid blocks.  Allow one extra space in the array, that
	   will map to the very end of the entire ballot.  Nota bene:
	   This map is not filled in here, but must be filled in
	   later before use.  This is done in main_screen.c.
	*/
	bc->map_physical_column_to_grid_block =
	    malloc((bc->num_physical_columns + 1)*sizeof(unsigned int));

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
		bc->num_candidates[split_party_index];

	    /* Keep track of previous split_party_index to identify
	       the end of the split data for a group. */
	    unsigned int last_split_party_index;

	    while (physical_column_index < bc->num_physical_columns) {

		/* Copy data until we get to the next split group. */
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
			    split_party_index =
				    atoi(PQgetvalue(result, split_index, 0));
			    split_candidate_count =
				    atoi(PQgetvalue(result, split_index, 2));
			}
		    } while ((split_index < num_splits) &&
			     (split_party_index == last_split_party_index));
		    /* Fill in remaining physical column
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

	PQclear(result);
	PQfinish(conn);

	return(bc);
}


