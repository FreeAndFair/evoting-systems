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
#include <string.h>
#include "message.h"
#include "keystroke.h"

static char *ordered_keystrokes = NULL;
static size_t keystroke_size;

static const char keymap[] = { [INPUT_UP] = 'U',
			       [INPUT_DOWN] = 'D',
			       [INPUT_NEXT] = 'N',
			       [INPUT_PREVIOUS] = 'P',
			       [INPUT_UNDO] = 'X',
			       [INPUT_SELECT] = 'S' };

static void store_keystroke(enum input_event key)
{
	char add[2];

	if (!ordered_keystrokes) {
		keystroke_size = 32;
		ordered_keystrokes = malloc(keystroke_size);
		ordered_keystrokes[0] = '\0';
	} else if (strlen(ordered_keystrokes) == keystroke_size-1) {
		keystroke_size *= 2;
		ordered_keystrokes = realloc(ordered_keystrokes,
					     keystroke_size);
	}
	if (!ordered_keystrokes)
		display_error(ERR_INTERNAL);

	/* Append this key */
	add[0] = keymap[key];
	add[1] = '\0';
	strcat(ordered_keystrokes, add);
}

/* DDS3.2.6: Interpret Keystroke */
enum input_event interpret_keystroke(void)
{
	enum input_event key;

	key = get_keystroke();

	if (key == INPUT_UP
	    || key == INPUT_DOWN
	    || key == INPUT_NEXT
	    || key == INPUT_PREVIOUS
	    || key == INPUT_UNDO
	    || key == INPUT_SELECT)
		store_keystroke(key);

	return key;
}

/* DDS3.2.10: Delete All Keystrokes */
void delete_keystrokes(void)
{
	free(ordered_keystrokes);
	ordered_keystrokes = NULL;
}

/* DDS3.2.26: Get Keystrokes */
const char *get_keystrokes(void)
{
	if (ordered_keystrokes == NULL) return "";
	else return ordered_keystrokes;
}
