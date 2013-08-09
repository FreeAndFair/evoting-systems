/* This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd */

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
#include "enter_paper.h"
#include <voting_client/initiate_session.h>
#include <voting_client/main_screen.h>
#include <voting_client/image.h>
#include "accumulate_deo_preferences.h"

/* DDS3.10: Enter Paper */
bool enter_paper(void)
{
	bool cancelled;

	if (!initialise_display(1152, 864, false)) bailout("Can't init display");
	/* Display main voting screen */
	dsp_mn_vt_scn();
	
	/* Allow DEO to complete ballot */
	cancelled = accumulate_deo_preferences();

	close_display();

	return cancelled;
}
