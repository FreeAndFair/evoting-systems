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
#include <common/database.h>
#include <common/evacs.h>
#include "check_for_repeats.h"
#include "check_votes.h"
#include "compare_votes.h"

/* DDS3.6: Check for Repeats */
bool check_for_repeats(void)
{
	PGconn *conn;
	unsigned int polling_place_code;
	bool loaded;

	/* Connect to master database from polling place */
	conn = connect_db(LOAD1DB_NAME);

	/* Extract the polling place code from the first vote */
	/* Should be the same for all votes */
	polling_place_code = SQL_singleton_int(conn,
					       "SELECT polling_place_code "
					       "FROM server_parameter "
					       "WHERE id= "
					       "    (SELECT MIN(id) "
					            "FROM  server_parameter);");
					                 
	PQfinish(conn);

	if ( polling_place_code < 0 )
		return false;

	/* Connect to evacs database to see if its already been loaded */

	conn = connect_db(DATABASE_NAME);
	/* DDS3.6: Get Polling Places Done */
	loaded = SQL_singleton_bool(conn,
				"SELECT loaded "
				"FROM polling_place "
				"WHERE code = %u;",
				polling_place_code);
	
	PQfinish(conn);
	
	return (loaded);
}

