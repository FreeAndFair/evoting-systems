#ifndef _HTTP_H
#define _HTTP_H
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
#include <stdint.h>
#include <common/voting_errors.h>

/* an array of these structures is returned and given to a http
   operation.  The final one must have name = value = NULL. */
struct http_vars {
	char *name;
	char *value;
};

/* Get a URL from the server.  Returns NULL on error, or the filename
   to be freed by the caller. */
extern char *http_get_file(const char *servername,
			   uint16_t portnum,
			   const char *page);

/* Get a URL from the server: returns the body (must be freed by caller) */
extern char *http_get(const char *servername,
		      uint16_t portnum,
		      const char *page,
		      size_t *size);

/* Pass the parameters to a CGI script, get the response, or NULL on error. */
/* Call must use http_free on returned value if non-NULL. */
extern struct http_vars *http_exchange(const char *servername,
				       uint16_t portnum,
				       const char *scripturl,
				       const struct http_vars *request_params);

/* Extract a variable. from the http vars.  NULL if not found. */
extern const char *http_string(const struct http_vars *hvars,
			       const char *name);

/* Every reply has an encoded error.  This finds it. */
extern enum error http_error(const struct http_vars *hvars);

/* Free the hvars returned from http_exchange */
extern void http_free(struct http_vars *hvars);

/* Decode an x-www-form-urlencoded string into an http_vars
 * associative array of key value pairs. */
extern struct http_vars *http_urldecode(const char *str);

/* Encodes an http_vars associative array into a x-www-form-urlencoded
   string.  Caller must free string. */
extern char *http_urlencode(const struct http_vars *hvars);
#endif /*_EXAMPLE_H*/
