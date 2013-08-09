#ifndef _INPUT_H
#define _INPUT_H
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
#include <stdbool.h>
#include <common/barcode.h>

/* This file encapsulates all the (X11) input processing */
enum input_event {
	INPUT_UP,
	INPUT_DOWN,
	INPUT_NEXT,
	INPUT_PREVIOUS,
	INPUT_SELECT,
	INPUT_FINISH,
	INPUT_UNDO,
	INPUT_START_AGAIN,
	INPUT_BARCODE,
	INPUT_UNUSED,
	INPUT_VOLUME_UP,
	INPUT_VOLUME_DOWN
};

/* Wait for a single keypress */
extern enum input_event get_keystroke(void);

/* Waiting for either a keypress or a barcode (in which case,
   bc->ascii filled in). */
extern enum input_event get_keystroke_or_barcode(struct barcode *bc);

/* Wait for end of the world */
extern void wait_for_reset(void) __attribute__((noreturn));

/* Initialize the input subsystem: returns false on failure. */
extern bool initialize_input(void);

/* Do reset: this is the correct way to exit the program. */
extern void do_reset(void) __attribute__((noreturn));

#endif /*_EXAMPLE_H*/
