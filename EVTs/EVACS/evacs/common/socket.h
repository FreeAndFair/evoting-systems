#ifndef _SOCKET_H
#define _SOCKET_H
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
#include <string.h>

/* Time (seconds) to time out operations */ 
#define SOCKET_TIMEOUT 5

/* Returns socket fd, or -1 on error/timeout */
extern int open_socket_out(const char *host, uint16_t port);

/* printf- like function for a socket.  Returns -1 on timeout */
extern int sock_printf(int sock, const char *format, ...)
__attribute__((format (printf,2,3)));

/* read to EOF on a socket, and return a buffer of bytes and the count.
   (NULL on error).
   Caller must free() returned value. */
extern void *sock_load(int sock, size_t *n);
#endif /*_SOCKET_H*/
