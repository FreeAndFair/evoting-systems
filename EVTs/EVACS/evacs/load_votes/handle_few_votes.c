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
#include <string.h>
#include <common/database.h>
#include <common/evacs.h>
#include <common/batch.h>
#include "handle_few_votes.h"
#include "check_votes.h"


/* Get votes from database */
/* SIPL 2011-08-29 Move any pre-poll votes to the specific
   pre-poll batch for the polling place. */
/* SIPL 2011-08-29 Additional parameters conn_master (to enable
   a lookup of the pre-poll polling place code),
   elec_date (the date of the election),
   and pre_poll_polling_place_code. */
static struct vote_list *get_votes(PGconn *conn_master,
				   char *elec_date,
				   unsigned int *num_rows,
				   unsigned int *polling_place_code,
				   int *pre_poll_polling_place_code,
				   unsigned int csc_code,
				   struct electorate *electorates)
{
	PGconn *conn=connect_db(LOAD1DB_NAME);
	PGresult *result;
	unsigned int i,j,rows, total_votes=0;
	struct vote_list *votes={NULL};
	struct electorate *current_electorate;
	char *old_batch_number, *new_batch_number;
	/* SIPL 2011-08-29 Batch number for pre-poll votes.*/
	char *pre_polling_batch_number;
	/* Get the polling place code for this loaded data */
	*polling_place_code = SQL_singleton_int(conn,
						"SELECT polling_place_code "
						"FROM server_parameter; "
						);
	/* SIPL 2011-08-29 Now look up the pre-poll polling place code
	   from the master database. */
	*pre_poll_polling_place_code = SQL_singleton_int(conn_master,
						"SELECT pre_polling_code "
						"FROM polling_place "
						"WHERE code=%u;",
						*polling_place_code
						);

	/*
	  Update polling place of all votes when the number of votes for
	   that electorate total less than 20.
	*/
	/* SIPL 2011-08-29 Now the 20-vote check must be done
	   separately for pre-poll and for polling-day votes. */
	begin(conn);
	for (current_electorate=electorates;
	     current_electorate;
	     current_electorate=current_electorate->next) {
		
		old_batch_number = sprintf_malloc("%u%03u000",
						  current_electorate->code,
						  *polling_place_code);
		new_batch_number = sprintf_malloc("%u%03u000",
						  current_electorate->code,
						  csc_code);
		/* DDS3.8: Save Polling Place with Few Votes */
		/* DDS3.8: Get Polling Place with Few Votes */
		/* Original code:
		j = SQL_command(conn,
				"UPDATE %s_confirmed_vote "
				"SET batch_number = %s "
				"WHERE batch_number "
				"IN (SELECT batch_number "
				      "FROM %s_confirmed_vote cv "
				      "WHERE 20 > (SELECT COUNT(*) "
				      "FROM %s_confirmed_vote "
				      "WHERE batch_number = "
				      "cv.batch_number));",
				current_electorate->name,
				new_batch_number,
				current_electorate->name,
				current_electorate->name);
		*/
		/* SIPL 2011-08-29 Now treat pre-poll and polling-day
		   votes separately. */
		j = SQL_command(conn,
				"UPDATE %s_confirmed_vote "
				"SET batch_number = %s "
				"WHERE batch_number "
				"IN (SELECT batch_number "
				      "FROM %s_confirmed_vote cv "
				      "WHERE 20 > (SELECT COUNT(*) "
				      "FROM %s_confirmed_vote "
				      "WHERE batch_number = "
				      "cv.batch_number "
				      "AND "
				      "to_date(time_stamp, "
				      "'YYYY-MM-DD HH24:MI:SS') "
				      "< to_date('%s', 'YYYY-MM-DD')))"
				"AND "
				"to_date(time_stamp, "
				"'YYYY-MM-DD HH24:MI:SS') "
				"< to_date('%s', 'YYYY-MM-DD');",
				current_electorate->name,
				new_batch_number,
				current_electorate->name,
				current_electorate->name,
				elec_date,
				elec_date);

		j = SQL_command(conn,
				"UPDATE %s_confirmed_vote "
				"SET batch_number = %s "
				"WHERE batch_number "
				"IN (SELECT batch_number "
				      "FROM %s_confirmed_vote cv "
				      "WHERE 20 > (SELECT COUNT(*) "
				      "FROM %s_confirmed_vote "
				      "WHERE batch_number = "
				      "cv.batch_number "
				      "AND "
				      "to_date(time_stamp, "
				      "'YYYY-MM-DD HH24:MI:SS') "
				      ">= to_date('%s', 'YYYY-MM-DD')))"
				"AND "
				"to_date(time_stamp, "
				"'YYYY-MM-DD HH24:MI:SS') "
				">= to_date('%s', 'YYYY-MM-DD');",
				current_electorate->name,
				new_batch_number,
				current_electorate->name,
				current_electorate->name,
				elec_date,
				elec_date);

		/* SIPL 2011-08-29 If there is pre-polling for this
		   polling place, move pre-poll votes to the corresponding
		   batch. Note, if there are fewer than 20 pre-poll votes,
		   they will already have been moved to Central Scrutiny,
		   so this will do nothing. */
		if (*pre_poll_polling_place_code >= 0) {
		  pre_polling_batch_number =
		    sprintf_malloc("%u%03u000",
				   current_electorate->code,
				   *pre_poll_polling_place_code);
		  j = SQL_command(conn,
				  "UPDATE %s_confirmed_vote "
				  "SET batch_number = %s "
				  "WHERE batch_number = %s "
				  "AND "
				  "to_date(time_stamp, "
				  "'YYYY-MM-DD HH24:MI:SS') "
				  "< to_date('%s', 'YYYY-MM-DD');",
				  current_electorate->name,
				  pre_polling_batch_number,
				  old_batch_number,
				  elec_date);
		} else
		  /* Set it to NULL so that the subsequent free()
		     will not be done. */
		  pre_polling_batch_number = NULL;
		  

		/* Load our 'view' of the database - with the updated rows */
		result = SQL_query(conn,
				   "SELECT batch_number,paper_version,time_stamp,preference_list "
				   "FROM %s_confirmed_vote;",current_electorate->name);
		
		rows = PQntuples(result);

		if ((int) rows < 1 )
		  continue;
		
		if (!votes)
		  votes = malloc(sizeof(*votes) + 
				 sizeof(struct vote) * (total_votes+rows));
		else 
		  votes = realloc(votes, sizeof(*votes) + 
				 sizeof(struct vote) * (total_votes+rows));
		
		for (i=0; i<rows; i++) {
			votes->vote[i+total_votes].batch_number 
				= atoi(PQgetvalue(result, i, 0));
			votes->vote[i+total_votes].paper_version 
				= atoi(PQgetvalue(result,i,1));
			votes->vote[i+total_votes].timestamp
				= malloc(sizeof(char) * (strlen(PQgetvalue(result,i,2))+1));
			strcpy(votes->vote[i+total_votes].timestamp,(char *)PQgetvalue(result,i,2));
			votes->vote[i+total_votes].preference_list
				= malloc(sizeof(char) * (strlen(PQgetvalue(result,i,3) )+1));
			votes->vote[i+total_votes].electorate_code=current_electorate->code;
			strcpy(votes->vote[i+total_votes].preference_list,(char *) PQgetvalue(result,i,3));
			
		}
		PQclear(result);
		free(old_batch_number);
		free(new_batch_number);
		free(pre_polling_batch_number);
		total_votes+=rows;
	}
		/* Don't permanently effect the load database! */
	rollback(conn);
	PQfinish(conn);
	
	*num_rows=total_votes;

	return votes;
}

/* DDS3.8: Copy Vote */
static void copy_vote(PGconn *conn, struct vote vote, 
		      unsigned int polling_place_code, 
		      struct electorate *electorate)
{
	unsigned int i;
	struct preference_set *preferences=unpack_preferences(vote.preference_list);


	SQL_command(conn,
		    "INSERT INTO %s_confirmed_vote"
		    "(batch_number,paper_version,time_stamp,preference_list) "
		    "VALUES(%u,%u,'%s','%s');",
		    electorate->name,
		    vote.batch_number,
		    vote.paper_version, 
		    vote.timestamp,
		    vote.preference_list);

	/* And in the confirmed vote table summary if required */
	if ( SQL_singleton_int(conn,"SELECT COUNT(*) "
			       "FROM vote_summary "
			       "WHERE electorate_code = %d "
			       "AND polling_place_code = %d;",
			       vote.electorate_code,polling_place_code)
	     == 0)
		SQL_command(conn,"INSERT INTO vote_summary "
			    "(electorate_code,polling_place_code,"
			    "entered_by,entered_at,informal_count) "
			    "VALUES (%d,%d,'EVACS','NOW',0);",
			    vote.electorate_code,polling_place_code);

	/* If no preferences - increment number of informal votes */
	if (!strlen(vote.preference_list))
		SQL_command(conn,"UPDATE vote_summary "
			    "SET informal_count = informal_count + 1,"
			        "entered_by = 'EVACS',"
			        "entered_at = 'NOW' "
			    "WHERE electorate_code = %d "
			    "AND polling_place_code = %d;",
			    vote.electorate_code,polling_place_code);

	
	for(i=0;i<preferences->num_preferences; i++)
	{
		/* Summarise first preferences for election night */
		if ( preferences->candidates[i].prefnum == 1) {
			if (SQL_singleton_int(conn,"SELECT COUNT(*) "
					      "FROM preference_summary "
					      "WHERE electorate_code = %d "
					      "AND polling_place_code = %d "
					      "AND party_index = %d "
					      "AND candidate_index = %d;",
					      vote.electorate_code,
					      polling_place_code,
					      preferences->candidates[i].group_index,
					      preferences->candidates[i].db_candidate_index)
			    == 0)
				SQL_command(conn,"INSERT INTO "
					    "preference_summary"
					    "(electorate_code,"
					    "polling_place_code,party_index,"
					    "candidate_index,phoned_primary,"
					    "evacs_primary,final_count) "
					    "VALUES(%d,%d,%d,%d,0,1,0);",
					    vote.electorate_code,
					    polling_place_code,
					    preferences->candidates[i].group_index,
					    preferences->candidates[i].db_candidate_index);
			else
				SQL_command(conn,"UPDATE "
					    "preference_summary "
					    "SET evacs_primary = "
					    "evacs_primary + 1 "
					    "WHERE electorate_code = %d "
					    "AND polling_place_code = %d "
					    "AND party_index = %d "
					    "AND candidate_index = %d;",
					    vote.electorate_code,
					    polling_place_code,
					    preferences->candidates[i].group_index,
					    preferences->candidates[i].db_candidate_index);
			SQL_command(conn,"UPDATE vote_summary "
				    "SET entered_by = 'EVACS',"
				    "entered_at = 'NOW' "
				    "WHERE electorate_code = %d "
				    "AND polling_place_code = %d;",
				    vote.electorate_code,
				    polling_place_code);
		}
	}
	free(preferences);
}

/* DDS3.8: Handle Few Votes */
void handle_few_votes(void)
{
	struct vote_list *votes;
	unsigned int num_votes,i,polling_place_code;
	/* SIPL 2011-08-29 Now also get the corresponding
	   pre-poll polling place code.  Note that the type
	   is int, as the special value -1 indicates that there
	   is no pre-poll code. */
	int pre_poll_polling_place_code;
	int num_elecs=0, num_rows,csc_code;
	struct electorate *electorates[100];
	struct electorate *elec_ptr, *elec_ptr_start;
	/* SIPL 2011-08-29 The date of the election. */
	char *elec_date;

	PGconn *conn=connect_db(DATABASE_NAME);
	
	/* SIPL 2011-08-29 Get the date of the election
	   from the master database. */
	elec_date = SQL_singleton(conn,
				  "SELECT to_date(election_date, "
				  "'DD Month YYYY') FROM master_data;");

	/* get all electorate data */
	elec_ptr=get_electorates(conn);
	elec_ptr_start = elec_ptr;

	/* convert to array for name lookups */
	for (;elec_ptr;elec_ptr=elec_ptr->next) 
	{
		electorates[elec_ptr->code]=elec_ptr;
		num_elecs++;
	}

	/* Get polling place to use when less than 20 votes in electorate */
	csc_code = resolve_polling_place_code(conn, "Central Scrutiny");

	if ( csc_code < 0 )
		/* The fallback CSC code is .. */
		csc_code = 400;
		/* bailout("Could not find code for Central Scrutiny "
		   "polling place"); */

	/* Get votes structure from the load database */
	votes = get_votes(conn,elec_date,&num_votes,&polling_place_code,
			  &pre_poll_polling_place_code,
			  (unsigned int)csc_code,elec_ptr_start);
		
	/* Start the transaction */
	begin(conn);

	/* Prevent race condition in SELECT - INSERT or UPDATE code */
	/* This won't block readers - only other writers */
	SQL_command(conn,"LOCK TABLE vote_summary IN EXCLUSIVE MODE;");
 	SQL_command(conn,"LOCK TABLE preference_summary IN EXCLUSIVE MODE;");

	
	fflush(stderr);
	/* Insert votes into counting database */
	for (i=0; i<num_votes; i++)
		copy_vote(conn, votes->vote[i],polling_place_code,
			  electorates[votes->vote[i].electorate_code]);
	
	for (i=0; i<num_votes; i++) {
		free(votes->vote[i].timestamp);
		free(votes->vote[i].preference_list);
	}
	free(votes);

	/* Mark polling place as loaded */
	num_rows = SQL_command(conn,"UPDATE polling_place "
			       "SET loaded = true "
			       "WHERE code = %u "
			       "AND loaded = false;",
			       polling_place_code);
	/* Sanity check - check that only one row was updated */
	if ( num_rows != 1 ) {
		rollback(conn);
		PQfinish(conn);
		if (num_rows == 0)
			bailout("This polling place has already been "
				"loaded!\n");
		else
			bailout("More than one entry exists for polling "
				"place code %u.\n",polling_place_code);
	}

	/* 2011-08-30 Now do the same for the pre-poll code, if there
	 is one. */
	if (pre_poll_polling_place_code >= 0) {
		num_rows = SQL_command(conn,"UPDATE polling_place "
				       "SET loaded = true "
				       "WHERE code = %u "
				       "AND loaded = false;",
				       pre_poll_polling_place_code);
		/* Sanity check - check that only one row was updated */
		if ( num_rows != 1 ) {
			rollback(conn);
			PQfinish(conn);
			if (num_rows == 0)
				bailout("This pre-poll polling place has "
					"already been loaded!\n");
			else
				bailout("More than one entry exists "
					"for pre-polling "
					"code %u.\n",
					pre_poll_polling_place_code);
		}
	}

        /* electorate codes start at 1 */
	for (i=1;i<num_elecs;i++ ) 
	{	
		free(electorates[i]);
	}
	/* SIPL 2011-08-29 Free storage for the election date. */
	free(elec_date);
	
	/* End the transaction */
	commit(conn);
       	PQfinish(conn);
	printf("Number of votes loaded = %u\n",num_votes);
}





