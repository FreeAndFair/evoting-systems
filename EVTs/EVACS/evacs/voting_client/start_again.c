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
#include <stdbool.h>
#include <unistd.h>
#include "start_again.h"
#include "initiate_session.h"
#include "message.h"
#include "image.h"
#include "input.h"
#include "vote_in_progress.h"
#include "keystroke.h"
#include "audio.h"

/* The want 10 pixels between YES and NO messages */
#define OPTION_SPACING 10

static bool restart = true;

/* DDS3.2.10: Format Start Again Screen */
static void format_start_again(void)
{
	unsigned int language, screen_width, x_coord, y_coord;
	struct image *sa_image, *yes_image, *no_image, *highlighted;

	language = get_language();

	/* Draw background */
	paste_image(0,0,get_message(language, MSG_BACKGROUND));
	
	sa_image = get_message(language, MSG_START_AGAIN_PROMPT);
	paste_image (0, 0, sa_image);
	
	screen_width = get_screen_width();
	
	yes_image = get_message(language, MSG_YES);
	
	x_coord = (screen_width / 2) - (image_width(yes_image) / 2);
	y_coord = image_height(sa_image);
	
	/* If decision is to  restart, the YES option is highlighted */
	if (restart) {
		highlighted = highlight_image(yes_image);
		paste_image(x_coord, y_coord, highlighted);
	}
	else {
		paste_image(x_coord, y_coord, yes_image);
	}
	
	no_image = get_message(language, MSG_NO);
	
	y_coord += image_height(yes_image) + OPTION_SPACING;

	/* If decision is NO, highlight the NO option */
	if (!restart) {
		highlighted = highlight_image(no_image);
		paste_image(x_coord, y_coord, highlighted);
	}
	else {
		paste_image(x_coord, y_coord, no_image);
	}
}	

/* DDS3.2.10: Update Start Again Cursor */
static void update_sa_cursor(void)
{
	restart = !restart;
}	


/* DDS3.2.10: Handle Start Again Screen */
bool start_again(void)
{
	enum input_event keystroke;
	const struct preference_set *vote_in_progress;
	
	/* If voting has not yet started, then just need to delete 
	   keystrokes */
	vote_in_progress = get_vote_in_progress();
	if (vote_in_progress->num_preferences == 0) {
		delete_keystrokes();
		return true;
	}
	restart = true;
	do {
		format_start_again();

		/* Audio message */
		if (restart)
			play_audio(true, get_audio("start_again_yes.raw"));
		else
			play_audio(true, get_audio("start_again_no.raw"));

		keystroke = get_keystroke();
		if ((keystroke == INPUT_UP) || (keystroke == INPUT_DOWN)) {
			update_sa_cursor();
		}
		else if (keystroke == INPUT_VOLUME_UP) {
			increase_volume();
		}
		else if (keystroke == INPUT_VOLUME_DOWN) {
			decrease_volume();
		}
	} while (keystroke != INPUT_SELECT);

	/* If YES option selected: */
	if (restart) {
		delete_keystrokes();
		delete_prefs();

		return true;
	}
	/* Voter decides not to start again */
	else {
		return false;
	}	
}
