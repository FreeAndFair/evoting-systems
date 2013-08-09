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
#include "voting_client.h"
#include "get_cursor.h"
#include "message.h"

#define CURSOR_CGI "/cgi-bin/get_initial_cursor"

static int cursor;

const int get_current_cursor(void)
{
	return cursor;
}

int get_initial_cursor(const struct electorate *elec)
{
  struct http_vars *reply;
  int initial_cursor;
  /* SIPL 2011-09-26 Added one to length of array.  There was
     no chance of a buffer overflow, but do this to make it consistent
     with all other uses of INT_CHARS. */
  char ecodestr[INT_CHARS+1];
  struct http_vars request[]
    = { { (char*)"ecode", ecodestr }, { NULL, NULL } };

  sprintf(ecodestr, "%u", elec->code);

  reply = http_exchange(SERVER_ADDRESS, SERVER_PORT, CURSOR_CGI,request);
  if (!reply)
    display_error(ERR_SERVER_UNREACHABLE);

  initial_cursor = atoi(http_string(reply, "cursor"));

  http_free(reply);

  cursor = initial_cursor;

  return initial_cursor;
}
