/* This file is (C) copyright 2001 Software Improvements, Pty Ltd,
   based on prototypes/Graph-c-booth/http.c by:
	Copyright (C) Andrew Tridgell 2001
   
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

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <common/evacs.h>
#include <common/http.h>
#include <common/rotation.h>
#include "voting_client.h"
#include "message.h"
#include "get_rotation.h"

#define ROBSON_CGI "/cgi-bin/get_rotation"

static struct rotation current_rotation;

/* DDS3.2.12: Get Current Rotation */
const struct rotation *get_current_rotation(void)
{
	return &current_rotation;
}


void set_current_rotation(const struct rotation *rot)
{
	current_rotation = *rot;
}

/* DDS3.2.6: Get Rotation */
void get_rotation(const struct electorate *elec)
{
	struct http_vars *reply;
	unsigned int i;
	/* SIPL 2011-09-26 Added one to length of array.  There was
	   no chance of a buffer overflow, but do this to make it consistent
	   with all other uses of INT_CHARS. */
	char ecodestr[INT_CHARS+1];
	struct http_vars request[]
		= { { (char*)"ecode", ecodestr }, { NULL, NULL } };

	sprintf(ecodestr, "%u", elec->code);

	reply = http_exchange(SERVER_ADDRESS, SERVER_PORT, ROBSON_CGI,request);
	if (!reply)
		display_error(ERR_SERVER_UNREACHABLE);

	/* Some error occurred? */
	if (http_error(reply))
		display_error(http_error(reply));

	for (i = 0; i < elec->num_seats; i++) {
		char varname[strlen("rotation")
			    + sizeof(STRINGIZE(MAX_ELECTORATE_SEATS))];
		const char *val;

		sprintf(varname, "rotation%u", i);
		val = http_string(reply, varname);
		current_rotation.rotations[i] = atoi(val);
		assert(current_rotation.rotations[i] < elec->num_seats);
	}
	/* DDS3.2.6: Save Rotation */
	current_rotation.size = elec->num_seats;
	http_free(reply);
}
