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
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
#include <common/evacs.h>
#include "http.h"
#include "socket.h"

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

/* Every reply has an encoded error.  This finds it. */
enum error http_error(const struct http_vars *hvars)
{
	const char *s = http_string(hvars, "error");

	if (!s) return ERR_SERVER_UNREACHABLE;
	return (enum error)atoi(s);
}

/* Frees an http_vars associative array. */
void http_free(struct http_vars *hvars)
{
	unsigned int i; 
	for (i=0; hvars[i].name; i++) {
		free(hvars[i].name);
		free(hvars[i].value);
	}
	free(hvars);
}

/**********************************************************/
/* http escaping and unescaping                           */
/**********************************************************/

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

/* Remove HTTP escapes from a string (in place). */
static void http_unescape(char *buf)
{
	char *p = buf;
	char *q = buf;

	while (p && *p) {
		int v;
		if (*p == '+') {
			*q++ = ' ';
			p++;
			continue;
		}
		if (*p == '%' && sscanf(p+1, "%02x", &v) == 1) {
			*q++ = (char)v;
			p += 3;
			continue;
		}
		*q++ = *p++;
	}

	*q = 0;
}

/* Decode an x-www-form-urlencoded string into an http_vars
 * associative array of key value pairs. */
struct http_vars *http_urldecode(const char *str)
{
	const char *s;
	struct http_vars *hvars;
	int nvars;
	int i;

	/* count number of variables */
	for (s=str, nvars=1; s && *s; s++) {
		if ((*s) == '&')
			nvars++;
	}

	hvars = malloc(sizeof(struct http_vars) * (nvars+1));
	if (!hvars)
		return NULL;
	memset(hvars, 0, sizeof(struct http_vars) * (nvars+1));
	
	for (i=0; i < nvars; i++) {
		char *s1=NULL, *s2;

		if (i < nvars-1) {
			s1 = strchr(str, '&');
			assert(s1);

			*s1 = '\0';
		}
			
		s2 = strchr(str, '=');

		if (!s2) {
			hvars[i].name = strdup(str);
			hvars[i].value = strdup("");
			/* Out of memory? */
			if (!hvars[i].name || !hvars[i].value) {
				http_free(hvars);
				return NULL;
			}
			http_unescape(hvars[i].name);
		} else {
			*s2++ = '\0';
			hvars[i].name = strdup(str);
			hvars[i].value = strdup(s2);
			/* Out of memory? */
			if (!hvars[i].name || !hvars[i].value) {
				http_free(hvars);
				return NULL;
			}
			http_unescape(hvars[i].name);
			http_unescape(hvars[i].value);
		}

		str = s1 + 1;
	}

	return hvars;
}

/* Copy body, given HTTP header and total response size.  Update
   response size to reflect body size, or return NULL. */
static char *http_parse_header(const char *p, size_t *n)
{
	int major, minor;
	int icode;
	char scode[21];
	char *body, *newbody;

	if (sscanf(p,"HTTP/%d.%d %3d %20s", 
		   &major, &minor, &icode, scode) != 4)
		return NULL;

	if (icode != 200)
		return NULL;

	/* Look for standard "first cr/linefeed pair */
	body = strstr(p, "\r\n\r\n");
	if (body) {
		body += 4;
	} else {
		/* Try standard "first cr" pair */
		body = strstr(p, "\n\n");
		if (body) body += 2;
		else
			/* No body found */
			return NULL;
	}

	/* Update length to reflect body length */
	*n -= (body - p);
	newbody = malloc(*n + 1);

	if (!newbody)
		return NULL;

	memcpy(newbody, body, *n);

	/* The returned body may contain nulls, but for the
	   convenience of other functions which treat it as a string,
	   make sure it is null-terminated */
	newbody[*n] = '\0';

	return newbody;
}	

/* Performs an HTTP GET operation on a given page and returns the
   retreived body. */
char *http_get(const char *servername,
	       uint16_t portnum,
	       const char *page,
	       size_t *size)
{
	int sock;
	size_t n;
	char *p, *body;

	sock = open_socket_out(servername, portnum);

	sock_printf(sock, "GET %s HTTP/1.0\r\n", page);
	sock_printf(sock, "User-Agent: EVACS booth\r\n\r\n");

	p = sock_load(sock, &n);
	close(sock);
	if (!p)
		return NULL;

	body = http_parse_header(p, &n);
	free(p);

	/* If they gave us a size, set it */
	if (size)
		*size = n;

	return body;
}

/* Performs an HTTP GET operation on a given page, and drop into a
   local (temporary) file.  Returns the filename (to be freed by the
   caller), or NULL. */
char *http_get_file(const char *servername,
		    uint16_t portnum,
		    const char *page)
{
	int fd;
	size_t n;
	char *fname = NULL;
	char *buf;

	buf = http_get(servername, portnum, page, &n);
	if (!buf)
		return NULL;
	
	fname = malloc(sizeof("/tmp/http%u") + INT_CHARS);
	if (!fname) {
		free(buf);
		return NULL;
	}
	sprintf(fname, "/tmp/http%u", getpid());

	fd = open(fname, O_WRONLY|O_CREAT|O_TRUNC, 0644);
	if (fd == -1) {
		free(buf);
		return NULL;
	}

	write(fd, buf, n);
	close(fd);
	free(buf);
	return fname;
}

/* Perform an HTTP POST operation on a given page and returns the
   retrieved body.  */
static char *http_post(const char *server,
		       uint16_t port,
		       const char *page,
		       const char *postdata,
		       size_t *size)
{
	int sock;
	char *p, *body;
	size_t n;

	sock = open_socket_out(server, port);
	if (sock < 0)
		return NULL;

	sock_printf(sock, "POST %s HTTP/1.0\r\n", page);
	sock_printf(sock, "User-Agent: EVACS booth\r\n");
	sock_printf(sock,
		    "Content-type: application/x-www-form-urlencoded\r\n");
	sock_printf(sock, "Content-length: %d\r\n\r\n",
		    strlen(postdata));
	sock_printf(sock, "%s", postdata);
	
	p = sock_load(sock, &n);
	close(sock);
	if (!p)
		return NULL;

	body = http_parse_header(p, &n);
	free(p);

	if (size)
		*size = n;

	return body;
}

/* Pass the parameters to a CGI script, get the response. */
struct http_vars *http_exchange(const char *servername,
				uint16_t portnum,
				const char *scripturl,
				const struct http_vars *request_params)
{
	char *query_string;
	char *reply;
	struct http_vars *reply_params;
	/* SIPL 2011: Changed type of n to conform to parameter type. */
	size_t n;

	query_string = http_urlencode(request_params);
	if (!query_string)
		return NULL;
	fprintf(stderr,"http_exchange:SERVER %s, PORT: %i, SCRIPTURL: %s, Qstring: %s\n",
		servername, portnum, scripturl, query_string);
	reply = http_post(servername, portnum, scripturl, query_string, &n);
	free(query_string);

	if (!reply) /* HTTP error */
		return NULL;

	reply_params = http_urldecode(reply);
	free(reply);

	return reply_params;		
}
