#ifndef _VOTING_SERVER_H
#define _VOTING_SERVER_H
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

/* Common routines and definitions for Voting Server */
#include <stdbool.h>
#include <common/voting_errors.h>

/* Location of the slave web server */
#define SLAVE_SERVER_ADDRESS "127.0.0.1"
#define SLAVE_SERVER_PORT 8081

/* Do I have a slave? */
extern bool am_i_master(void);

/* Function for CGI scripts to get database server, port. */
extern const char *get_database_port(void);
#endif /*_VOTING_SERVER_H*/
