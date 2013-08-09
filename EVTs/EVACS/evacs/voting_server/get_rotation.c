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

/* This CGI is invoked by the client to get the next robson rotation
   for the current electorate. */
#include <stdlib.h>
#include <string.h>
#include <common/rotation.h>
#include <common/database.h>
#include "fetch_rotation.h"
#include "cgi.h"

static struct rotation fetch_next_rotation(PGconn *conn,unsigned int ecode)
{
	int seat_count,rotation_num;
	struct rotation *rotation, rot;
	char *sn;

	/* Get seat count for this electorate */
	seat_count = SQL_singleton_int(conn,
				       "SELECT seat_count "
				       "FROM electorate "
				       "WHERE code = %u;",ecode);
	if (seat_count == -1)
	  bailout("Could not get number of seats for electorate %u.\n",
		      ecode);

	/* Get next robson rotation number */
	/* DDS3.2.5: Update Rotation Indices */
	rotation_num = get_seq_nextval(conn,sn=sprintf_malloc("robson_%d_seq",
							      seat_count)) + 1; 
	free(sn);

	/* Get the rotation */
	rotation = fetch_rotation(conn, rotation_num, seat_count);
	if (!rotation) {
		bailout("Could not get rotation number %u "
			"for %u seat electorate.\n",
			rotation_num, seat_count);
	}
	rot = *rotation;
	free(rotation);
	return rot;
}

static void send_rotation(const struct rotation *rot)
{
	char rotations[rot->size][sizeof("rotation") + INT_CHARS];
	/* SIPL 2011-09-26 Added one to length of array.  There was
	   no chance of a buffer overflow, but do this to make it consistent
	   with all other uses of INT_CHARS. */
	char rot_values[rot->size][INT_CHARS+1];
	struct http_vars vars[rot->size+1];
	unsigned int i;

	for (i = 0; i < rot->size; i++) {
		sprintf(rotations[i], "rotation%u", i);
		sprintf(rot_values[i], "%u", rot->rotations[i]);
		vars[i].name = rotations[i];
		vars[i].value = rot_values[i];
	}
	/* Terminate variables */
	vars[i].name = vars[i].value = NULL;

	cgi_good_response(vars);
}

int main(int argc, char *argv[])
{
	struct http_vars *vars;
	struct rotation rot;
	PGconn *conn;

	/* Our own failure function */
	set_cgi_bailout();

	vars = cgi_get_arguments();

	/* Connect to database  */
	conn = connect_db("evacs");
	if (!conn || PQstatus(conn) == CONNECTION_BAD)
		bailout("Could not open database\n");

	/* Get next rotation and update count here... */
	rot = fetch_next_rotation(conn,atoi(http_string(vars, "ecode")));
	http_free(vars);

	/* Encode to return */
	send_rotation(&rot);

	PQfinish(conn);
	return 0;
}

