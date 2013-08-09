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

#define main xmain
#include "check_votes.c"
#undef main


int main()
{
	/* TEST DDS999998 */
	PGconn *conn;
	char *db_name;
	unsigned int i,j;
	
	conn = connect_db("template1");
	SQL_command_nobail(conn,"drop database %s;",LOAD1DB_NAME);
	SQL_command(conn,"create database %s;",LOAD1DB_NAME);
	SQL_command_nobail(conn,"drop database %s;",LOAD2DB_NAME);
	SQL_command(conn,"create database %s;",LOAD2DB_NAME);

	PQfinish(conn);

	for (i=1;i<3;i++) {
		db_name = sprintf_malloc("evacs%u",i);
		conn = connect_db(db_name);
		free(db_name);

		/* Need our own slightly different definitions of the
	 	   confirmed_vote and confirmed_preference tables since
		   the "real" definitions prevent the tables from being
		   updated via a CHECK constraint.
		*/
	
		create_table(conn,"confirmed_vote",
			     "id INTEGER NOT NULL PRIMARY KEY,"
			     "electorate_code INTEGER NOT NULL,"
			     "polling_place_code INTEGER NOT NULL");


		create_table(conn,"confirmed_preference",
			     "vote_id INTEGER NOT NULL "
			     "REFERENCES confirmed_vote(id),"
			     "group_index INTEGER NOT NULL,"
			     "db_candidate_index INTEGER NOT NULL,"
			     "prefnum INTEGER NOT NULL CHECK(prefnum BETWEEN 1 AND 99)");

		/* 2 matching votes but different order */
		if ( i == 1) {
			SQL_command(conn, "INSERT into confirmed_vote"
				    "(id,electorate_code,"
				    "polling_place_code) "
				    "values (1,0,0);");
			/* 3 prefs for vote_id=1 */
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (1,1,0,1);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum,group_index,"
				    "db_candidate_index) "
				    "values (1,2,0,2);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (1,3,0,3);");

			SQL_command(conn, "INSERT into confirmed_vote"
				    "(id,electorate_code,"
				    "polling_place_code) "
				    "values (2,1,1);");

			/* 3 prefs for vote_id=2 */
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (2,1,0,1);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (2,2,0,2);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (2,3,0,3);");

		}
		else {
			SQL_command(conn, "INSERT into confirmed_vote"
				    "(id,electorate_code,"
				    "polling_place_code) "
				    "values (1,1,1);");
			/* 3 prefs for vote_id=1 */
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (1,1,0,1);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (1,2,0,2);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (1,3,0,3);");

			SQL_command(conn, "INSERT into confirmed_vote"
				    "(id,electorate_code,"
				    "polling_place_code) "
				    "values (2,0,0);");
			/* 3 prefs for vote_id=2 */
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (2,1,0,1);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum,group_index,"
				    "db_candidate_index) "
				    "values (2,2,0,2);");
			SQL_command(conn, "INSERT into confirmed_preference"
				    "(vote_id,prefnum, group_index,"
				    "db_candidate_index) "
				    "values (2,3,0,3);");
		}
		       

		PQfinish(conn);
		
	}

/* confirm matching votes */	
	if (!check_votes())
		exit(1);

/* set up non-matching preference in table2*/
	conn = connect_db("evacs2");
	SQL_command(conn, "UPDATE confirmed_preference "
		    "SET group_index=12 "
		    "WHERE vote_id=2  "
		    "AND prefnum=1;");
	PQfinish(conn);

	/* check that the votes now do not match (preference) */
	 if (check_votes())
		 exit(2); 
    
	 /* restore matching  preference in table2*/
	conn = connect_db("evacs2");
	SQL_command(conn, "UPDATE confirmed_preference "
		    "SET group_index=0 "
		    "WHERE vote_id=2  "
		    "AND prefnum=1;");
	PQfinish(conn);

	/* check the preferences now match as expected */
	if (!check_votes())
		exit(3);

/* set up a non-matching vote (wrong electorate)*/
	for (i=1;i<3;i++) {
		db_name = sprintf_malloc("evacs%u",i);
		conn = connect_db(db_name);
		SQL_command(conn, "INSERT into confirmed_vote"
			    "(id,electorate_code, polling_place_code) "
			    "values (3,%u,0)  ",(i-1));
		SQL_command(conn, "INSERT into confirmed_preference"
			    "(vote_id,prefnum, group_index,"
			    "db_candidate_index) "
			    "values (3,1,0,1)  ");
		PQfinish(conn);	
	}

	/* check that the votes now do not match (electorate) */
	 if (check_votes())
		 exit(3); 

	 /* Correct non-matching vote */
	 conn = connect_db("evacs1");
	 SQL_command(conn,
		     "UPDATE confirmed_vote "
		     "SET electorate_code = 1 "
		     "WHERE id = 3;");
	 PQfinish(conn);

	 /* Check that the votes now match as expected */
	 if (!check_votes())
		 exit(4);

	 /* set up a non-matching vote (wrong Polling place)*/
	for (i=1;i<3;i++) {
		db_name = sprintf_malloc("evacs%u",i);
		conn = connect_db(db_name);

		SQL_command(conn, "UPDATE confirmed_vote "
			    "SET polling_place_code=%u "
			    "WHERE id=3;",(i-1));

		PQfinish(conn);	
	}
 
	/* check that the votes still do not match (polling_place) */
	if (check_votes())
		exit(5);
 
	 /* Correct non-matching vote */
	 conn = connect_db("evacs1");
	 SQL_command(conn,
		     "UPDATE confirmed_vote "
		     "SET polling_place_code = 1 "
		     "WHERE id = 3;");
	 PQfinish(conn);

	 /* Check that the votes now match as expected */
	 if (!check_votes())
		 exit(6);
	 
	 /* Insert an extra vote into evacs1 */
	 conn = connect_db("evacs1");
	 SQL_command(conn, "INSERT into confirmed_vote"
		     "(id,electorate_code, polling_place_code) "
		     "values (4,0,0);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (4,1,0,1)  ");
	 PQfinish(conn);
	
	 /* Check that the votes DO NOT match as expected */
	 if (check_votes())
		 exit(7);
 
	 /* Insert the same vote into evacs2 */
	 conn = connect_db("evacs2");
	 SQL_command(conn, "INSERT into confirmed_vote"
		     "(id,electorate_code, polling_place_code) "
		     "values (4,0,0);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (4,1,0,1)  ");
	 PQfinish(conn);

	 /* Check that the votes match as expected */
	 if (!check_votes())
		 exit(8);

	 /* Insert donkey vote into evacs2 */
	 conn = connect_db("evacs2");
	 SQL_command(conn, "INSERT into confirmed_vote"
		     "(id,electorate_code, polling_place_code) "
		     "values (5,0,0);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (5,1,0,0)  ");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (5,2,0,1)  ");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (5,3,0,2)  ");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (5,4,0,3)  ");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (5,5,0,4)  ");
	 PQfinish(conn);

	 /* Followed by a stack of votes in BOTH databases */
	 for (i=1;i<=2;i++) {
		 db_name = sprintf_malloc("evacs%u",i);
		 conn = connect_db(db_name);
		 free(db_name);
		 for (j=4;j<=18;j++) {
			 SQL_command(conn, "INSERT into confirmed_vote"
				     "(id,electorate_code,"
				     "polling_place_code) "
				     "values (%u,4,8);",j+i);
			 SQL_command(conn, "INSERT into confirmed_preference"
				     "(vote_id,prefnum, group_index,"
				     "db_candidate_index) "
				     "values (%u,9,9,1);",j+i);
		 }
		 PQfinish(conn);
	 }	

 	 /* Insert donkey vote into evacs1 as vote 20 */
	 conn = connect_db("evacs1");
	 SQL_command(conn, "INSERT into confirmed_vote"
		     "(id,electorate_code, polling_place_code) "
		     "values (20,0,0);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (20,1,0,0);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (20,2,0,1);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (20,3,0,2);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (20,4,0,3);");
	 SQL_command(conn, "INSERT into confirmed_preference"
		     "(vote_id,prefnum, group_index,"
		     "db_candidate_index) "
		     "values (20,5,0,4);");
	 PQfinish(conn);

	 /* Check that the votes STILL match as expected */
	 if (!check_votes())
		 exit(8);


	 exit(0);
}






