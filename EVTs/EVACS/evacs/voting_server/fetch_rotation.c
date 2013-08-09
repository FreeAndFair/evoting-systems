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
#include <stdlib.h>
/*#include <common/safe.h>*/
#include "fetch_rotation.h"

struct rotation *fetch_rotation(PGconn *conn,
				unsigned int rotation_num,
				unsigned int seat_count)
{
	struct rotation *rot;
	char *rotstring;

	/* Get the rotation */
	rotstring = SQL_singleton(conn,
				 "SELECT rotation "
				 "FROM robson_rotation_%u "
				 "WHERE rotation_num = %u;",
				 seat_count, rotation_num);
	if (rotstring == NULL)
		return NULL;

	rot = malloc(sizeof(*rot));
	rot->size = seat_count;

	/* rotation is in the form {n,n,n,n,n} */
	if ( seat_count == 5 ) { /* 5 seat electorate */
		sscanf(rotstring, "{%u,%u,%u,%u,%u}",
		       &rot->rotations[0],
		       &rot->rotations[1],
		       &rot->rotations[2],
		       &rot->rotations[3],
		       &rot->rotations[4]);
	} else { /* Assume 7 seat electorate */
		sscanf(rotstring, "{%u,%u,%u,%u,%u,%u,%u}",
		       &rot->rotations[0],
		       &rot->rotations[1],
		       &rot->rotations[2],
		       &rot->rotations[3],
		       &rot->rotations[4],
		       &rot->rotations[5],
		       &rot->rotations[6]);
	}

	free(rotstring);
	return rot;
}
