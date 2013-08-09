/* This file is (C) copyright 2001 Software Improvements, Pty Ltd.
   
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
#include <string.h>
#include <time.h>
#include <common/barcode.h>
#include <common/database.h>
#include <common/createtables.h>

#include "save_and_verify.c"

/*
  This program is run as a child many times by multiuser_save_and_verify_tests
  to test multiple users attempting to vote simultaneously.
*/

/* TEST DDS3.2.22: Save And Verify Vote */
int main(int argc, char *argv[])
{
	struct preference_set vote_in;
	struct barcode bc;
	struct electorate elec;
	unsigned int err;

	PGconn *conn;

	conn = connect_db("evacs");

	/* Passed barcode text from caller? */
	if ( argc > 1 ){
		memset(bc.data,'\0',sizeof(bc.data));
		strcpy(bc.data,argv[1]);
	}
	else
		/* Use the same barcode for all children */
		strcpy(bc.data,"Multi_user_barcode");
	elec.code = 0;

	vote_in.num_preferences = 5;
	vote_in.candidates[0].group_index = 0;
	vote_in.candidates[0].db_candidate_index = 0;
	vote_in.candidates[0].prefnum = 1;
	vote_in.candidates[1].group_index = 1;
	vote_in.candidates[1].db_candidate_index = 1;
	vote_in.candidates[1].prefnum = 2;
	vote_in.candidates[2].group_index = 2;
	vote_in.candidates[2].db_candidate_index = 2;
	vote_in.candidates[2].prefnum = 3;
	vote_in.candidates[3].group_index = 3;
	vote_in.candidates[3].db_candidate_index = 3;
	vote_in.candidates[3].prefnum = 4;
	vote_in.candidates[4].group_index = 4;
	vote_in.candidates[4].db_candidate_index = 4;
	vote_in.candidates[4].prefnum = 5;

	/* Wait here until parent process unlocks the master row */

	SQL_command(conn,"UPDATE barcode "
		    "SET electorate_code = 1 "
		    "WHERE electorate_code = 1;");

	/* and they're racing .... */

        err = primary_store_start(conn, &vote_in, &bc, &elec);
	if (err != ERR_OK) {
      		primary_store_abort(conn);
		PQfinish(conn);
		exit(1);
	}
	else
		err = primary_store_commit(conn);
	PQfinish(conn);
	exit(0);
}
