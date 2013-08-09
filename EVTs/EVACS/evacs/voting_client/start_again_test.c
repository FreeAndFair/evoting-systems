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
#include "start_again.c"
#include <stdlib.h>

unsigned int number_of_keystrokes;
static unsigned int language = 0;
static enum input_event ks;
bool slow;
 
static struct preference_set vote_in_progress =
{ .num_preferences = 0 };

void get_event(void);

void get_event(void)
{
	return;
}

unsigned int get_language(void)
{
	return(language);
}          

/* Wait for end of the world */
void wait_for_reset(void)
{
        /* get_event handles RESET internally */
        while (true) get_event();
}


enum input_event get_keystroke(void)
{
	if (slow) sleep(1);
	if (number_of_keystrokes-- > 0)
		return ks;
	else
		return INPUT_SELECT;
}

void delete_prefs(void)
{
	vote_in_progress.num_preferences = 0;
}

const struct preference_set *get_vote_in_progress(void)
{
	return &vote_in_progress;
}

int main(int argc, char *argv[])
{
	bool restart;

	if (argc == 2) {
		slow = true;
	}

	audio_init();
	if (!initialise_display(false))
		exit(1);

	/* TEST DDS3.2.10: Format Start Again Screen */
	format_start_again();
	if (slow) sleep(3);
		
	clear_screen();

	/* TEST DDS3.2.10: Handle Start Again Screen */
	
	restart = start_again();
	if (!restart) exit(1);

	vote_in_progress.num_preferences = 3;
	number_of_keystrokes = 5;
	ks = INPUT_DOWN;
	restart = start_again();

	if (restart) exit(1);

	clear_screen();
	number_of_keystrokes = 4;
	ks = INPUT_DOWN;
	restart = start_again();
	if (!restart) exit(1);

	vote_in_progress.num_preferences = 3;
	clear_screen();	
	number_of_keystrokes = 4;
	ks = INPUT_UP;
	restart = start_again();
	if (!restart) exit(1);

	vote_in_progress.num_preferences = 3;
	clear_screen();	
	number_of_keystrokes = 7;
	ks = INPUT_UP;
	restart = start_again();
	if (restart) exit(1);
	
	/* TEST DDS3.2.10: Update Start Again Cursor */
	update_sa_cursor();
	if (restart) exit(1);

	exit(0);
}
