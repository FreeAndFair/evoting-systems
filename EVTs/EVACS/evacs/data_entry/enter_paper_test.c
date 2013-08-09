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
#include <stdlib.h>
#define accumulate_deo_preferences dummy1
#include "accumulate_deo_preferences.c"
#undef accumulate_deo_preferences
#include "enter_paper.c"

bool prefs_deleted, main_screen_displayed, prefs_accumulated; 

/* Stubs */
void dsp_mn_vt_scn(void)
{
	main_screen_displayed = true;
}

bool accumulate_deo_preferences(void)
{
	prefs_accumulated = true;
	return false;
}

int main()
{
	bool cancelled;

	prefs_accumulated =  main_screen_displayed = false;

	/* TEST DDS3.10: Enter Paper */
	cancelled = enter_paper();
	if ((prefs_accumulated == false)  
	    || (main_screen_displayed == false))
		exit(1);
	if (cancelled) exit (1);

	exit(0);
}
