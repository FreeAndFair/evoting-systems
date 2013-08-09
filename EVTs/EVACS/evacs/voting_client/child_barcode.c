/* This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd,
   based on prototypes/Graph-c-booth/barcode.c:
	   Copyright (C) David Gibson 2001
*/

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
#include <stdlib.h>
#include <stdbool.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <termios.h>
#include <unistd.h>
#include <sys/param.h>
#include <fcntl.h>
#include <X11/Xlib.h>
#include "child_barcode.h"

#ifndef SERIAL_DEVICE
#define SERIAL_DEVICE     "/dev/ttyS0"
#define USB_SERIAL_DEVICE "/dev/ttyUSB0"
#endif

/* Our error handling here is simple.  Print message and exit.  Parent
   will realise that we have died, and act accordingly (message only
   useful for debugging). */
static void fatal(const char *fmt, ...)
__attribute__ ((noreturn, format (printf, 1, 2)));

static void fatal(const char *fmt, ...)
{
	va_list arglist;

	/* Prepend "FATAL: " to the error message */
	fprintf(stderr, "FATAL: ");

	/* Simply pass argument list onto vfprintf to print error */
	va_start(arglist, fmt);
	vfprintf(stderr, fmt, arglist);
	va_end(arglist);

	exit(1);
}

/* Open serial port and set it to the correct values. */
static int open_serial(const char *dev)
{
	int fd, rc;
	struct termios tio;

	fd = open(dev, O_RDONLY);
	if (fd == -1)
		fatal("Unable to open %s: %s (%d)\n",
		      dev, strerror(errno), errno);

	/* Get original attributes */
	rc = tcgetattr(fd, &tio);
	if (rc != 0)
		fatal("Failed tcgetattr(): %s (%d)\n",
		      strerror(errno), errno);

	/* Set it to RAW mode, and 9600 baud */
	cfmakeraw(&tio);
	rc = cfsetispeed(&tio, B9600);
	if (rc != 0)
		fatal("Failed cfsetispeed(): %s (%d)\n",
		      strerror(errno), errno);
	
	/* Write attributes back */
	rc = tcsetattr(fd, TCSAFLUSH, &tio);
	if (rc != 0)
		fatal("Failed tcsetattr(): %s (%d)\n",
		      strerror(errno), errno);

	return fd;
}

/* Send one barcode to the parent */
static void send_barcode(Display *display,
			 const char *barcode,
			 int pipe_to_parent)
{
	XEvent ev;

	/* Do whole thing in one write.  If less than PIPE_BUF, it
           will appear at the other end in a single read, and won't
           block at this end. */
	if (write(pipe_to_parent, barcode, strlen(barcode)+1)
	    != strlen(barcode)+1)
		fatal("Failed to write barcode to pipe: %s\n",
		      strerror(errno));

	/* Set up X event to send to parent */
	bzero(&ev, sizeof(ev));
	ev.type = ClientMessage;
	ev.xclient.message_type = XInternAtom(display, "barcode", False);
	ev.xclient.format = 8;

	if (!XSendEvent(display, InputFocus, True, 0, &ev))
		fatal("Error on XSendEvent\n");

	/* Flush to make sure it arrives */
	XSync(display, False);
}

static void read_barcode(Display *display, int serial_fd, int pipe_to_parent)
__attribute__((noreturn));

/* DDS????: Read Barcode */
static void read_barcode(Display *display, int serial_fd, int pipe_to_parent)
{
	char buf[128];
	char barcode[PIPE_BUF+1];
	int codesize = 0;

	while (true) {
		ssize_t n;
		unsigned int i;

		/* Read from serial device.  Expect to block here */
		n = read(serial_fd, buf, sizeof(buf));
		if (n <= 0)
			fatal("Error reading serial device: %s (%d)\n",
			      n ? strerror(errno) : "(no data)", errno);

		/* Iterate through contents, and transfer to barcode */
		for (i = 0; i < n; i++) {
                        if (buf[i] == '\n') { /* New-style reader */
                          /* Skip it */
                          continue;
			} else if (buf[i] == '\r') {
                          /* We have a whole barcode */
				barcode[codesize] = '\0';
				send_barcode(display, barcode, pipe_to_parent);
				codesize = 0;
			} else {
				/* If we got confused, reset */
				if (codesize == sizeof(barcode)-1)
					codesize = 0;
				barcode[codesize++] = buf[i];
			}
		}
	}
}

void child_barcode(int pipe_to_parent)
{
	Display *disp;
	int serial_fd;

	/* "Autodetect the barcode reader by trying to open the USB serial device first
		then the serial barcode */
	serial_fd = open(USB_SERIAL_DEVICE, O_RDONLY);
	if ((serial_fd == -1) && (errno == ENOENT)) {
	  /* serial barcode reader */
	  serial_fd = open_serial(SERIAL_DEVICE);
	}
	else {
	  /* close and reopen to USB barcode reader to fix issue where first
		  character of barcode reader is lost during first barcode swipe */
	  close(serial_fd);
	  serial_fd = open_serial(USB_SERIAL_DEVICE);
	}

	/* Open X display to send events to parent */
	disp = XOpenDisplay(NULL);
	if (!disp) fatal("Can't open display");

	/* We're setup: call home. */
	write(pipe_to_parent, "OK", 1);

	read_barcode(disp, serial_fd, pipe_to_parent);
}
