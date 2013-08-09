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
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include "get_paper_version.h"
#include <common/current_paper_index.h>
#include <common/voter_electorate.h>
#include <voting_server/fetch_rotation.h>
#include <common/evacs.h>


unsigned int get_integer(void)
{
	char *reply;
	unsigned int i;

	reply = fgets_malloc(stdin);
       
	i = atoi(reply);
	free(reply);

	return i;
}


struct rotation *get_rotation_from_pvn(const struct electorate *elec, 
				       unsigned int pvn)
{
	static struct rotation *rot;
	PGconn *conn;
	
	conn = connect_db_host(DATABASE_NAME,SERVER_ADDRESS);
	if (!conn) {
	  bailout("Cant connect to database %s at %s",
		  DATABASE_NAME,
		  SERVER_ADDRESS);		  
	}
	
	rot = fetch_rotation(conn, pvn, elec->num_seats);

	PQfinish(conn);

	return rot;
	
}


/* DDS3.8: Start New Paper */
/* DDS3.8: Get Paper Version Number */
int get_paper_version(void)
{
	const struct electorate *batch_electorate;
	struct rotation *rotation;
	unsigned int paper_version_number=-1;
	bool VersionOK = false;
	const char bell = 0x7;

	batch_electorate = get_voter_electorate();
	
	while (!VersionOK) {
		printf("\nPlease enter the paper version of paper number %u"
		       ":> ",get_current_paper_index());
		fflush(stdout);
		
		paper_version_number = get_integer();
				
		rotation = get_rotation_from_pvn(batch_electorate,
						paper_version_number);
		if (rotation) {
			VersionOK = true;
		} else {
			if (paper_version_number == END_BATCH_CODE) {
				free(rotation);
				return -1;
			}
			printf("%cPaper version %u not found; "
			       "please enter another> ",bell ,paper_version_number);
		}
	}
	free(rotation);
	return paper_version_number;
}
	






