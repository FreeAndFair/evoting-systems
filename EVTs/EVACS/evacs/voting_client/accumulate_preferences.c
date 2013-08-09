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
#include "accumulate_preferences.h"
#include "message.h"
#include "image.h"
#include "input.h"
#include "verify_barcode.h"
#include "get_rotation.h"
#include "get_cursor.h"
#include "main_screen.h"
#include "keystroke.h"
#include "undo_pref.h"
#include "add_preference.h"
#include "move_cursor.h"
#include "start_again.h"
#include "initiate_session.h"
#include "draw_group_entry.h"
#include "audio.h"

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

	/* Play the acknowledgement */
	play_audio(true, get_audio("ack.raw"));
	sleep(10);
}


void accumulate_preferences(void)
{
	const struct electorate *electorate;
	enum input_event key;
	bool restart, continue_voting= true;
	struct cursor cursor;
	unsigned int language;
	struct cursor default_cursor;

	electorate = get_voter_electorate();
	get_rotation(electorate);

	default_cursor.screen_candidate_index = -1;
	default_cursor.group_index = get_initial_cursor(electorate);

	set_cursor_position(default_cursor);


	/* Audio for the first time on the main voting screen */
	play_audio(true,
		   get_audio("electorates/%u/main_screen.raw",
			     electorate->code));
	dsp_mn_vt_scn();
	/* Do not interrupt intro audio */
	draw_group_entry(default_cursor, YES, false);

	while(continue_voting == true) {
		key = interpret_keystroke();
		
		if (key == INPUT_UNDO) {
			undo_pref();
		}
		else if (key == INPUT_SELECT) {
			add_preference();
		}
		else if (key == INPUT_START_AGAIN) {
			cursor = get_cursor_position();
			restart = start_again();
			dsp_mn_vt_scn();
			if (restart) {
				play_audio(true,
					   get_audio("started_again.raw"));
				set_cursor_position(default_cursor);
				/* Do not interrupt started again message */
				draw_group_entry(default_cursor, YES, false);
			}
			/* If not restarting, highlight last cursor position */
			else {
				play_audio(true,
					   get_audio("not_started_again.raw"));
				/* Don't interrupt audio */
				draw_group_entry(cursor, YES, false);
			}
		}
		else if (key == INPUT_FINISH) {
			language = get_language();
			cursor = get_cursor_position();
			continue_voting = confirm_and_commit_vote(language);
			if (continue_voting) {
				dsp_mn_vt_scn();
				/* Audio for the main voting screen */
				play_audio(true,
					   get_audio("%u/main_screen.raw",
						     electorate->code));
				/* Do not interrupt main screen speil */
				draw_group_entry(cursor, YES, false);
			}
		}
		else if (key == INPUT_VOLUME_UP) {
			increase_volume();
		}
		else if (key == INPUT_VOLUME_DOWN) {
			decrease_volume();
		}
		else {
			move_cursor(key);
		}
	}
	
}

