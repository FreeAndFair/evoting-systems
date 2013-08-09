#ifndef _CGI_H
#define _CGI_H
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
/* This file covers the server's http interactions */
#include <common/http.h>

/* Get cgi variables (must be a POST).  Caller must free variables. */
extern struct http_vars *cgi_get_arguments(void);

/* Provide a positive http response (and exits). */
extern void cgi_good_response(const struct http_vars *vars);

/* Provide a negative http response (and exits). */
extern void cgi_error_response(enum error err);

/* Set up own bailout function */
extern void set_cgi_bailout(void);
#endif /*_EXAMPLE_H*/
