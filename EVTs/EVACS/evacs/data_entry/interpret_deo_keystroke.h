#ifndef _INTERPRET_DEO_KEYSTROKE_H
#define _INTERPRET_DEO_KEYSTROKE_H
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

/* This file encapsulates all the (X11) deo_keystroke processing */

#define DEO_END_BATCH_KEYSTROKE_ENTER  (unsigned int )NULL
#define DEO_END_BATCH_KEYSTROKE_y      89
#define DEO_END_BATCH_KEYSTROKE_Y     121 
#define	DEO_END_BATCH_KEYSTROKE_n     110
#define	DEO_END_BATCH_KEYSTROKE_N      78

enum deo_keystroke {
	DEO_KEYSTROKE_0,
	DEO_KEYSTROKE_1,
	DEO_KEYSTROKE_2,
	DEO_KEYSTROKE_3,
	DEO_KEYSTROKE_4,
	DEO_KEYSTROKE_5,
	DEO_KEYSTROKE_6,
	DEO_KEYSTROKE_7,
	DEO_KEYSTROKE_8,
	DEO_KEYSTROKE_9,
	DEO_KEYSTROKE_DOWN,
	DEO_KEYSTROKE_UP,
	DEO_KEYSTROKE_NEXT,
	DEO_KEYSTROKE_CANCEL_PAPER,
	DEO_KEYSTROKE_FINISH_PAPER,   
	DEO_KEYSTROKE_DELETE
	};

/* Wait for a single keypress */
extern enum deo_keystroke interpret_deo_keystroke(void);

#endif /*_INTERPRET_DEO_KEYSTROKE_H*/



