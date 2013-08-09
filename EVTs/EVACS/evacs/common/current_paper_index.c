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

/* this file contains accessors to a static variable current_paper_index */

#include "current_paper_index.h"

/* global indexing the current papers' order in the current batch (1-based)*/
static unsigned int current_paper_index=1;

void set_current_paper_index(unsigned int index)
{
	current_paper_index = index;
}

/* DDSv2B 3.6: Clear Current Paper Index   */
/* Evacs 2002: paper Index starts from 1 */
void clear_current_paper_index(void)
{
	set_current_paper_index(1);
}


/* DDSv2B 3.6: Update Current Paper Index   */
void update_current_paper_index(void)
{
	set_current_paper_index(get_current_paper_index()+1);
}

/* DDSv2B 3.22: Get Current Paper Index    */
unsigned int get_current_paper_index(void)
{
	return current_paper_index;
}
