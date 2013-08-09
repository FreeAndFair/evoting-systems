#ifndef _MOVE_CURSOR_H
#define _MOVE_CURSOR_H
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
#include "input.h"
#include "voting_client.h"
#include <common/cursor.h>

/* Get Cursor Position */
extern struct cursor get_cursor_position(void);

/* Set Cursor Position */
extern void set_cursor_position(struct cursor cp);

/* Move Cursor */
extern void move_cursor(enum input_event next);

#endif /*_MOVE_CURSOR_H*/
