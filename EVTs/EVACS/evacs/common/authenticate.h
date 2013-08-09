#ifndef _AUTHENTICATE_H
#define _AUTHENTICATE_H
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

/* This file contains authenticate functions, used by voting client
   and server */
#include <stdint.h>
#include <string.h>
#include <common/evacs.h>
#include <common/barcode.h>

#define AUTHENTICATE_CGI "/cgi-bin/authenticate"

struct http_vars;

/* Function to get http server, port.  The definition differs between
   voting client and voting server. */
extern const char *get_server(void);
extern uint16_t get_port(void);

/* Authenticate this barcode: fills in elecp (to be freed by caller),
   or returns != ERR_OK. */
enum error authenticate(const struct barcode *bc, struct electorate **elecp);
#endif /*_AUTHENTICATE_H*/
