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

/* This file contains routines to 'boil down' votes into summaries*/

#include <libpq-fe.h>
#include <common/database.h>
#include <common/batch.h>

#include "update_ens_summaries.h"


void update_vote_summary(PGconn *conn, 
			 struct normalised_preference *np,
			 unsigned int polling_place_code, 
			 unsigned int electorate_code)
{
	/* save vote in the confirmed vote table summary if required */
	if ( SQL_singleton_int(conn,"SELECT COUNT(*) "
			       "FROM vote_summary "
			       "WHERE electorate_code = %d "
			       "AND polling_place_code = %d;",
			       electorate_code,polling_place_code)
	     == 0)
		SQL_command(conn,"INSERT INTO vote_summary "
			    "(electorate_code,polling_place_code,"
			    "entered_by,entered_at,informal_count) "
			    "VALUES (%d,%d,'EVACS batch','NOW',0);",
			    electorate_code,polling_place_code);
	
	/* If no preferences - increment number of informal votes */
	if (np->n.num_preferences == 0)
		SQL_command(conn,"UPDATE vote_summary "
			    "SET informal_count = informal_count + 1,"
			    "entered_by = 'EVACS batch',"
			    "entered_at = 'NOW' "
			    "WHERE electorate_code = %d "
			    "AND polling_place_code = %d;",
			    electorate_code,polling_place_code);
	
}

void update_preference_summary(PGconn *conn,
			       struct preference *p,
			       unsigned int polling_place_code, 
			       unsigned int electorate_code)
{
	/* Summarise first preferences for election night */
	if ( p->prefnum == 1) {
		if (SQL_singleton_int(conn,"SELECT COUNT(*) "
				      "FROM preference_summary "
				      "WHERE electorate_code = %d "
				      "AND polling_place_code = %d "
				      "AND party_index = %d "
				      "AND candidate_index = %d;",
				      electorate_code,
				      polling_place_code,
				      p->group_index,
				      p->db_candidate_index)
		    == 0)
			SQL_command(conn,"INSERT INTO "
				    "preference_summary"
				    "(electorate_code,"
				    "polling_place_code,party_index,"
				    "candidate_index,phoned_primary,"
				    "evacs_primary,final_count) "
				    "VALUES(%d,%d,%d,%d,0,1,0);",
				    electorate_code,
				    polling_place_code,
				    p->group_index,
				    p->db_candidate_index);
		else
			SQL_command(conn,"UPDATE "
				    "preference_summary "
				    "SET evacs_primary = "
				    "evacs_primary + 1 "
				    "WHERE electorate_code = %d "
				    "AND polling_place_code = %d "
				    "AND party_index = %d "
				    "AND candidate_index = %d;",
				    electorate_code,
				    polling_place_code,
				    p->group_index,
				    p->db_candidate_index);
		SQL_command(conn,
			    "UPDATE vote_summary "
			    "SET entered_by = 'EVACS batch',"
			    "entered_at = 'NOW' "
			    "WHERE electorate_code = %d "
			    "AND polling_place_code = %d;",
			    electorate_code,polling_place_code);       
	}
	
}
