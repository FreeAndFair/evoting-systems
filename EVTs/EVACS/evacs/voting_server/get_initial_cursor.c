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

/* This CGI is invoked by the client to get the next cursor position
   for the current electorate. */
#include <stdlib.h>
#include <string.h>
#include <common/database.h>
#include <common/evacs.h>
#include "cgi.h"

static int fetch_next_cursor(PGconn *conn,unsigned int ecode)
{
  char *name;
  char *sn;
  PGresult *result;
  int cursor;

  /* Get seat count for this electorate */
  result = SQL_query(conn,
		     "SELECT name "
		     "FROM electorate "
		     "WHERE code = %u;",ecode);
  if (PQntuples(result) == 0)
    bailout("Could not get name for electorate %u.\n",
	    ecode);
  name = PQgetvalue(result, 0, 0);

  cursor = get_seq_nextval(conn,sn=sprintf_malloc("%s_cursor_seq",
						  name));
  free(sn);

  PQclear(result);

  return cursor;
}

static void send_cursor(const int *cursor)
{
  struct http_vars vars[2];

  /* SIPL 2011: These two lines (now commented out) were not correct,
     as the second assignment statement did not copy into the allocated
     space! */
  /* vars[0].name = malloc(sizeof("cursor")); */
  /* vars[0].name = "cursor"; */
  char cursor_string[] = "cursor";
  vars[0].name = cursor_string;
  /* SIPL 2011-09-26 Added one to length of array.  There was
     no chance of a buffer overflow, but do this to make it consistent
     with all other uses of INT_CHARS. */
  vars[0].value = malloc(INT_CHARS + 1);
  sprintf(vars[0].value, "%u", *cursor);
  vars[1].name = NULL;
  vars[1].value = NULL;

  cgi_good_response(vars);
}

int main(int argc, char *argv[])
{
  struct http_vars *vars;
  int cursor;
  PGconn *conn;

  /* Our own failure function */
  set_cgi_bailout();

  vars = cgi_get_arguments();

  /* Connect to database  */
  conn = connect_db("evacs");
  if (!conn || PQstatus(conn) == CONNECTION_BAD)
    bailout("Could not open database\n");

  /* Get next rotation and update count here... */
  cursor = fetch_next_cursor(conn,atoi(http_string(vars, "ecode")));
  http_free(vars);

  /* Encode to return */
  send_cursor(&cursor);

  PQfinish(conn);
  return 0;
}
