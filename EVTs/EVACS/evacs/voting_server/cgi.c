/* This file is (C) copyright 2001 Software Improvements, Pty Ltd.
   
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
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <common/evacs.h>
#include <common/socket.h>
#include "cgi.h"

/* Get cgi variables (must be a POST).  Caller must free variables. */
struct http_vars *cgi_get_arguments(void)
{
	const char *len;
	char *buffer;
	unsigned int todo, done;

	/* If this is not set, it's not a post, or no input */
	len = getenv("CONTENT_LENGTH");
	if (!len) return NULL;

	todo = atoi(len);
	buffer = malloc(todo+1);
	if (!buffer)
		bailout("Malloc of %u bytes failed in cgi_get_arguments\n",
			todo+1);

	/* Read in a loop... */
	done = 0;
	while (done < todo) {
		int r;
		r = read(STDIN_FILENO, buffer+done, todo);
		if (r <= 0)
			bailout("Read failed in cgi_get_arguments: %s\n",
				strerror(errno));
		done += r;
		todo -= r;
	}
	buffer[done] = '\0';

	return http_urldecode(buffer);
}

/* Actually do the CGI response */
static void cgi_respond(enum error err, const struct http_vars *vars)
{
	char *str, errcode[sizeof("error=%u&") + INT_CHARS];

	sprintf(errcode, "error=%u", (unsigned int)err);
	str = http_urlencode(vars);
	if (!str) bailout("Could not encode response\n");
	if (strlen(str) != 0) strcat(errcode, "&");

	sock_printf(STDOUT_FILENO,
		    "Content-type: application/x-www-form-urlencoded\r\n");
	sock_printf(STDOUT_FILENO, "Content-length: %u\r\n\r\n",
		    strlen(errcode) + strlen(str));

	sock_printf(STDOUT_FILENO, "%s%s", errcode, str);
	free(str);
}

/* Provide a positive http response. */
void cgi_good_response(const struct http_vars *vars)
{
	cgi_respond(ERR_OK, vars);
	exit(0);
}


/* Provide a negative http response. */

/* SIPL 2011: added noreturn attribute, as cgi_bailout() has one. */
void cgi_error_response(enum error err)
__attribute__((noreturn));

void cgi_error_response(enum error err)
{
	struct http_vars var = { NULL, NULL };

	cgi_respond(err, &var);
	exit(0);
}

static void cgi_bailout(const char *fmt, va_list arglist)
__attribute__((noreturn));

static void cgi_bailout(const char *fmt, va_list arglist)
{
	static int bailing_out = 0;
  
	/* Prevent recursion */
	if (bailing_out) exit(1);

	bailing_out = 1;
	fprintf(stderr,"FATAL: ");
  
	/* Pass argument list onto vfprintf to print error */
	vfprintf(stderr,fmt,arglist);

	cgi_error_response(ERR_SERVER_INTERNAL);
	
}

void set_cgi_bailout(void)
{
	/* Use our bailout function, which attempts to return an error */
	set_bailout(&cgi_bailout);
}
