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
#include <unistd.h>
#include <common/voter_electorate.h>
#include <common/cursor.h>
#include <common/ballot_contents.h>
#include "accumulate_preferences.h"
#include "message.h"
#include "image.h"
#include "get_rotation.h"
#include "main_screen.h"
#include "initiate_session.h"
#include "draw_group_entry.h"

void show_ballot(const struct electorate *electorate, const struct ballot_contents *bc);
extern void display_screen(const struct electorate *electorate, const struct ballot_contents *bc);
extern void get_dummy_rotation(const struct electorate *elec);

/* DDS3.2.6: Display Acknowledgement Screen */
void display_ack_screen(void)
{
	struct image *image;
	unsigned int language;

	language = get_language();
	/* Draw background */
	paste_image(0, 0, get_message(language, MSG_BACKGROUND));

	/* Draw acknowledgement in centre of screen */
	image = get_message(language, MSG_ACKNOWLEDGEMENT);
	paste_image((get_screen_width()-image_width(image))/2,
		    (get_screen_height()-image_height(image))/2,
		    image);

}


void show_ballot(const struct electorate *electorate, const struct ballot_contents *bc)
{
	const struct cursor default_cursor
		= { .group_index = 0, .screen_candidate_index = -1 };


	get_dummy_rotation(electorate);
	clear_screen();
	display_screen(electorate, bc);
	draw_group_entry(default_cursor, YES, false);
}


