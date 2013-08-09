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
#include <voting_client/image.h>
#include <voting_client/message.h>
#include <voting_client/main_screen.h>
#include <voting_client/draw_group_entry.h>
#include "interpret_deo_keystroke.h"
#include "move_deo_cursor.h"
#include "update_deo_preference.h"
#include "delete_deo_preference.h"
#include "prompts.h"

#include "accumulate_deo_preferences.h"

/* DDS3.14: Handle CANCEL PAPER Screen */
static bool display_cancel_paper_screen(void)
{
	struct image *message;
	enum deo_keystroke key;
	struct cursor cursor, default_cursor;
	
	cursor = get_cursor_position();
	default_cursor.group_index = DEFAULT_DEO_CURSOR_X;
	default_cursor.screen_candidate_index = DEFAULT_DEO_CURSOR_Y;

	/*clear_screen();*/
	message = get_cancel_prompt();
	paste_image(0,0,message);

	while (1) {
		key = interpret_deo_keystroke();
		/* DEO is sure */
		if (key == DEO_KEYSTROKE_DELETE) {
			clear_screen();
			reset_deo_cursor();
			return true;
		}
		/* DEO changes its mind */
		else if (key == DEO_KEYSTROKE_DOWN) {
			/*clear_screen();*/
			dsp_mn_vt_scn();
			draw_group_entry(default_cursor, NO, NO);
			draw_group_entry(cursor, YES, NO);
			return false;
		}
	}
}

/* DDS3.14: Handle END PAPER Screen */
static bool handle_end_paper_screen(void)
{
	struct image *message;
	enum deo_keystroke key;
	struct cursor cursor, default_cursor;
	
	cursor = get_cursor_position();
	default_cursor.group_index = DEFAULT_DEO_CURSOR_X;
	default_cursor.screen_candidate_index = DEFAULT_DEO_CURSOR_Y;
	
	/*clear_screen();*/
	message = get_finish_prompt();
	paste_image(0,0,message);

	while (1) {
		key = interpret_deo_keystroke();
		/* DEO is sure */
		if (key == DEO_KEYSTROKE_DELETE) {
			clear_screen();
			reset_deo_cursor();
			return true;
		}
		/* DEO changes its mind */
		else if (key == DEO_KEYSTROKE_DOWN) {
			/*clear_screen();*/
			dsp_mn_vt_scn();
			draw_group_entry(default_cursor, NO, NO);
			draw_group_entry(cursor, YES, NO);
			return false;
		}
	}
}
		

/* DDS3.14: Accumulate DEO Preferences */
bool accumulate_deo_preferences(void)
{
	bool paper_complete = false;
	enum deo_keystroke key;
	bool cancelled = false;
	
	draw_group_entry(get_cursor_position(),YES,false);
	while (!paper_complete) {
		key = interpret_deo_keystroke();
		if ((key == DEO_KEYSTROKE_DOWN) || (key == DEO_KEYSTROKE_UP) 
		    || (key == DEO_KEYSTROKE_NEXT)) {
			move_deo_cursor(key);
		}
		else if (key == DEO_KEYSTROKE_CANCEL_PAPER) {
			cancelled =  display_cancel_paper_screen();
			paper_complete = cancelled;
		}
		else if (key == DEO_KEYSTROKE_FINISH_PAPER) {
			paper_complete = handle_end_paper_screen();
		}
		else if (key == DEO_KEYSTROKE_DELETE) {
			delete_deo_preference();
		}
		else {
			update_deo_preference(key);
		}
	}

	return cancelled;

}
