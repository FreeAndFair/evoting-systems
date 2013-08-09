#ifndef _MOVE_DEO_CURSOR_H
#define _MOVE_DEO_CURSOR_H
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
#include <common/cursor.h>
#include "interpret_deo_keystroke.h"

#define DEFAULT_DEO_CURSOR_X 0
#define DEFAULT_DEO_CURSOR_Y 0

/* Update DEO Cursor Position */
extern void update_deo_cursor_position(struct cursor cp, 
				       enum deo_keystroke key);

extern void reset_deo_cursor(void);

/* Move DEO Cursor */
extern void move_deo_cursor(enum deo_keystroke key);


extern struct cursor get_cursor_position(void);


extern void set_cursor_position(struct cursor cursor_position);


#endif /*_MOVE_DEO_CURSOR_H*/
