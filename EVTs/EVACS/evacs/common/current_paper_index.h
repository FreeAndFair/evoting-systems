#ifndef _CURRENT_PAPER_INDEX
#define _CURRENT_PAPER_INDEX
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

/* This file defines the prototypes for accessing current_paper_index */


/* DDSv2B 3.22: Get Current Paper Index    */
extern unsigned int get_current_paper_index(void);

extern void set_current_paper_index(unsigned int index);

/* DDSv2B 3.6: Clear Current Paper Index   */
extern void clear_current_paper_index(void);

/* DDSv2B 3.6: Update Current Paper Index   */
extern void update_current_paper_index(void);


#endif /*  _CURRENT_PAPER_INDEX  */

