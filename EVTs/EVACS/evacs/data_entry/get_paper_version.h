#ifndef _GET_PAPER_VERSION_H
#define _GET_PAPER_VERISON_H
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
#define END_BATCH_CODE 999

struct electorate;

/* Get Paper Version Number */
extern int get_paper_version(void);

/* Get Rotation from Paper Version Number */
extern struct rotation *get_rotation_from_pvn(const struct electorate *elec, 
					      unsigned int pvn);

/* Get Integer from Standard Input */
extern unsigned int get_integer(void);

#endif /*_GET_PAPER_VERSION_H*/




