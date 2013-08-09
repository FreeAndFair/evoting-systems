#ifndef _GET_ROTATION_H
#define _GET_ROTATION_H
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

/* set rotation  */
extern void set_current_rotation(const struct rotation *rot);

/* Get the current rotation */
extern const struct rotation *get_current_rotation(void);

/* Called by accumulate_preferences to get the rotation from the server */
extern void get_rotation(const struct electorate *elec);
#endif /*_GET_ROTATION_H*/
