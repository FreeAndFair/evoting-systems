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

/* This CGI is invoked by the client to get the next robson rotation
   for the current electorate. */
#define fetch_next_rotation _fetch_next_rotation
extern int xmain(int argc, char *argv[]);
#define main xmain
#include "get_initial_cursor.c"
#undef main
#include <common/createtables.h>
#include <setjmp.h>
#include <assert.h>

#if 0
#define exit(x) { fprintf(stderr, "%u\n", __LINE__); exit(x); }
#endif

static bool interactive;
static struct http_vars http_vars[] = { { (char *)"ecode", (char *)"0" },
					 { NULL, NULL } };

/* stub */
void cgi_good_response(const struct http_vars *vars)
{
	if (interactive) {
		printf("error=0&%s", http_urlencode(vars));
		exit(0);
	}
	if (strcmp(vars[0].name, "cursor") != 0) exit(1);
	if (vars[1].name != NULL) exit(1);

	/* Should get "normal" rotation */
	if (atoi(vars[0].value) != 0) exit(1);
	if (vars[1].value != NULL) exit(1);
	exit(0);
}

void cgi_error_response(enum error err)
{
	abort();
}

struct http_vars *cgi_get_arguments(void)
{
	return http_vars;
}

void http_free(struct http_vars *vars)
{
	if (vars != http_vars) exit(1);
}

/* Retrieve a string value from an http_vars associative array.
   Returns NULL on failure.  */
const char *http_string(const struct http_vars *hvars, const char *name)
{
	unsigned int i;

	for (i=0; hvars && hvars[i].name; i++)
		if (strcmp(name, hvars[i].name) == 0) return hvars[i].value;

	/* Not found. */
	return NULL;
}

/*
 * List of characters which must be escaped in a x-www-form-urlencoded string
 */
#define UNSAFE_CHARACTERS "+&=%/"

/* Encodes an http_vars associative array into a x-www-form-urlencoded
   string.  Caller must free string. */
char *http_urlencode(const struct http_vars *hvars)
{
	const char hex[16] = "0123456789ABCDEF";
	unsigned int length = 0;
	char *buf, *s;
	unsigned int i;

	/* Count number of escapes required */
	for (i=0; hvars[i].name; i++) {
		char *tmp;
		int nunsafe = 0;

		tmp = strpbrk(hvars[i].name, UNSAFE_CHARACTERS);
		while (tmp) {
			nunsafe++;
			tmp = strpbrk(tmp + 1, UNSAFE_CHARACTERS);
		}

		tmp = strpbrk(hvars[i].value, UNSAFE_CHARACTERS);
		while (tmp) {
			nunsafe++;
			tmp = strpbrk(tmp + 1, UNSAFE_CHARACTERS);
		}

		length += strlen(hvars[i].name) +
			strlen(hvars[i].value) +
			nunsafe*2 + 1 + (i?1:0);
	}

	/* Allocate buffer */
	buf = malloc(length + 1);
	if (!buf) return NULL;
	s = buf;

	/* Write out variables, and do escapes */
	for (i=0; hvars && hvars[i].name; i++) {
		char *p;

		/* & separates variable names (after first one) */
		if (i != 0)
			*s++ = '&';

		for (p = hvars[i].name; *p; p++) {
			if (strchr(UNSAFE_CHARACTERS, *p)) {
				*s++ = '%';
				*s++ = hex[*p >> 4];
				*s++ = hex[*p & 0xf];
			} else if (*p == ' ')
				*s++ = '+';
			else
				*s++ = *p;
		}
		
		*s++ = '=';

		for (p = hvars[i].value; *p; p++) {
			if (strchr(UNSAFE_CHARACTERS, *p)) {
				*s++ = '%';
				*s++ = hex[*p >> 4];
				*s++ = hex[*p & 0xf];
			} else if (*p == ' ')
				*s++ = '+';
			else
				*s++ = *p;
		}
	}

	*s = '\0';

	assert (s == buf + length);

	return buf;
}

extern void set_cgi_bailout(void)
{
	/* Abort is fine for testing */
}

int main(int argc, char *argv[])
{
	PGconn *conn;

	conn = clean_database("evacs");

	drop_table(conn,"electorate");
	create_table(conn,
		     "electorate", 
		     "code INTEGER PRIMARY KEY,"
		     "name TEXT NOT NULL UNIQUE,"
		     "seat_count INTEGER NOT NULL");
	SQL_command(conn,
		    "INSERT INTO electorate VALUES ( %u, '%s', %u );",
		    0, "Molonglo", 7);
	drop_table(conn,"party");
	SQL_command(conn,"CREATE TABLE party ("
		    "electorate_code INTEGER NOT NULL "
		    "REFERENCES electorate(code),"
		    "index INTEGER NOT NULL,"
		    "name TEXT NOT NULL,"
		       "PRIMARY KEY(electorate_code,index));");
	SQL_command(conn,
		    "INSERT INTO party VALUES ( 0, 0, 'First Party' );");
	SQL_command(conn,
		    "INSERT INTO party VALUES ( 0, 1, 'Second Party' );");
	SQL_command(conn,
		    "INSERT INTO party VALUES ( 0, 2, 'Third Party' );");
	SQL_command(conn,
		    "INSERT INTO party VALUES ( 0, 3, 'Fourth Party' );");
	SQL_command(conn,
		    "INSERT INTO party VALUES ( 0, 4, 'Fifth Party' );");


	SQL_command(conn,
		    "CREATE SEQUENCE %s_cursor_seq START 0 "
		    "MINVALUE 0 MAXVALUE %d CYCLE;",
		    "Molonglo",
		    4);

	if (argc == 1) {
		int cursor;

		interactive = 0;
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 0) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 1) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 2) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 3) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 4) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 0) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 1) exit(1);
		cursor = fetch_next_cursor(conn, 0);
		if (cursor != 2) exit(1);
	} else {
		/* Do the whole thing */
		interactive = 1;
		xmain(argc, argv);
	}

	PQfinish(conn);
	return 0;
}

