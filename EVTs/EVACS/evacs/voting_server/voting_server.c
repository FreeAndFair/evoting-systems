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
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <common/authenticate.h>
#include "voting_server.h"

/* Slave is on different port */
#define SLAVE_DATABASE_PORT "5433"
#define MASTER_DATABASE_PORT ""

/* DDS3.2.26: Am I Master */
bool am_i_master(void)
{
	/* Apache sets SERVER_PORT environment variable for us */
	assert(getenv("SERVER_PORT"));
	if (atoi(getenv("SERVER_PORT")) == SLAVE_SERVER_PORT)
		return false;
	return true;
}

const char *get_database_port(void)
{
	if (am_i_master()) return MASTER_DATABASE_PORT;
	else return SLAVE_DATABASE_PORT;
}

/* Function for CGI scripts to get http server, port. */
const char *get_server(void)
{
	if (am_i_master()) return SERVER_ADDRESS;
	else return SLAVE_SERVER_ADDRESS;
}

uint16_t get_port(void)
{
	if (am_i_master()) return SERVER_PORT;
	else return SLAVE_SERVER_PORT;
}

