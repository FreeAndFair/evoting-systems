/* This file is (C) copyright 2001 Software Improvements, Pty Ltd,
   based on prototypes/Graph-c-booth/socket.c by:
	Copyright (C) 1998-2001 Andrew Tridgell
  
   (derived from rsync socket code)

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
#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>
#include <sys/poll.h>
#include <sys/time.h>
#include <signal.h>
#include <netdb.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
/* SIPL 2011: Additional include required. */
#include <linux/limits.h>

#include "socket.h"

/* Set if alarm goes off */
static volatile int alarmed = 0;

static void alarm_sig(int signum)
{
	/* Some things want to know if alarm went off */
	alarmed = 1;
}

/* open_socket_out()
 *
 * open a socket to a tcp remote host with the specified port.
 * Return the fd (>= 0), or -1 if an error occurs */
int open_socket_out(const char *host, uint16_t port)
{
	struct sockaddr_in sock_out;
	struct hostent *hp;
	int res;

	res = socket(PF_INET, SOCK_STREAM, 0);
	if (res == -1)
		return -1;

	/* Setup timeout: use half the time for the name lookup. */
	signal(SIGALRM, alarm_sig);
	alarm(SOCKET_TIMEOUT/2);

	hp = gethostbyname(host);
	if (!hp) {
		/* Terminate signal handler. */
		alarm(0);
		return -1;
	}

	memcpy(&sock_out.sin_addr, hp->h_addr, hp->h_length);
	sock_out.sin_port = htons(port);
	sock_out.sin_family = PF_INET;

	/* Use "larger"half the time for the connection. */
	alarm((SOCKET_TIMEOUT+1)/2);

	if (connect(res, (struct sockaddr *)&sock_out, sizeof(sock_out))) {
		/* Terminate signal handler. */
		alarm(0);
		return -1;
	}

	/* Terminate signal handler. */
	alarm(0);
	return res;
}

/* sock_write()
 *
 * write all bytes from a buffer to a socket, looping as necessary,
 * with alarm if neccessary.  */
static ssize_t sock_write(int sock, const void *buf, size_t n)
{
	ssize_t total = 0;

	/* Setup timeout. */
	alarmed = 0;
	signal(SIGALRM, alarm_sig);
	alarm(SOCKET_TIMEOUT);

	while (n) {
		ssize_t r = write(sock, buf, n);

		if (r == -1 || alarmed) {
			/* Terminate signal handler. */
			alarm(0);
			return -1;
		}
		if (r == 0) {
			/* Terminate signal handler. */
			alarm(0);
			return total;
		}

		n -= r;
		buf += r;
		total += r;
	}
	/* Terminate signal handler. */
	alarm(0);
	return total;
}

/* printf- like function for a socket.  Returns -1 on timeout */
int sock_printf(int sock, const char *format, ...)
{
	va_list ap;
	int n;
	char *p;

	/* work out how long it is going to be/ */
	va_start(ap, format);

	/* This won't write anything (length = 0), but returns the
	   number of bytes it would have taken. */
	n = vsnprintf(NULL, 0, format, ap);
	va_end(ap);

	if (n == 0)
		return 0;
	p = malloc(n+1);
	if (!p)
		return -1;

	/* Do the actual print into our string */
	va_start(ap, format);
	vsnprintf(p, n+1, format, ap);
	va_end(ap);

	if (sock_write(sock, p, n) != n) {
		free(p);
		return -1;
	}
	
	free(p);
	return n;
}

/* read to EOF on a socket, and return a buffer of bytes and the count */
void *sock_load(int sock, unsigned int *n)
{
	char *p;
	int r;
	char buf[PIPE_BUF];
	struct pollfd pfd;
	unsigned timeout;
	struct timeval start, now, diff;

	/* Under Linux 2.2, the signal delivery doesn't occur if there
	   are no bytes yet to read, so we use poll timeouts here. */
	pfd.fd = sock;
	pfd.events = POLLIN;
	*n = 0;

	/* Timeout is millisecond. */
	timeout = SOCKET_TIMEOUT * 1000;

	/* Figure out start time */
	gettimeofday(&start, NULL);

	/* Do a malloc to begin, so we have room for nul terminator */
	p = malloc(1);
	if (!p)
		return NULL;

	/* Poll returns the number of fds which are ready */
	while (poll(&pfd, 1, timeout) == 1) {
		char *newp;

		r = read(sock, buf, sizeof(buf));
		/* End of file reached? */
		if (r == 0) {
			/* nul-terminate string */
			p[*n] = '\0';
			return p;
		} else if (r < 0) {
			goto fail;
		}

		/* Copy into the returned buffer */
		newp = realloc(p, *n + r + 1);
		if (p == NULL)
		{
		  return NULL;
		}
		if (!newp)
			goto fail;
		p = newp;

		memcpy(p + (*n), buf, r);
		(*n) += r;

		/* Figure out time left */
		gettimeofday(&now, NULL);
		timersub(&now, &start, &diff);

		/* Convert to milliseconds */
		timeout -= diff.tv_usec / 1000 + diff.tv_sec * 1000;
		start = now;
	}
 fail:
	/* Error or timeout */
	free(p);
	return NULL;
}
