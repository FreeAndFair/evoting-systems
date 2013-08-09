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

/* This file implements  the (X11) deo_keystroke processing */
#include <stdbool.h>
#include <unistd.h>
#include <assert.h>
#include <X11/Xlib.h>
#include <X11/keysym.h>
#include <common/safe.h>
#include <voting_client/image.h>
#include "interpret_deo_keystroke.h"


struct deo_keymap
{
	unsigned int xkey;
	enum deo_keystroke evacs_key;
};


/* 2011-06-07 Modified to work with evdev keyboard driver. */
struct deo_keymap deo_keymap[] = {
	{90,DEO_KEYSTROKE_0},
	{87,DEO_KEYSTROKE_1},
	{88,DEO_KEYSTROKE_2},
	{89,DEO_KEYSTROKE_3},
	{83,DEO_KEYSTROKE_4},
	{84,DEO_KEYSTROKE_5},
	{85,DEO_KEYSTROKE_6},
	{79,DEO_KEYSTROKE_7},
	{80,DEO_KEYSTROKE_8},
	{81,DEO_KEYSTROKE_9},
	{104,DEO_KEYSTROKE_DOWN},
	{82,DEO_KEYSTROKE_UP},
	{86,DEO_KEYSTROKE_NEXT},
	{63,DEO_KEYSTROKE_CANCEL_PAPER},
	{106,DEO_KEYSTROKE_FINISH_PAPER},
	{91,DEO_KEYSTROKE_DELETE},
	
};

static XEvent get_deo_event(void)
{
	XEvent event;

	XNextEvent(get_display(), &event);

	return event;
}

/* Return the map for a give X keycode, or NULL if it's not in the map */
static struct deo_keymap *deo_map_key(unsigned int keycode)
{
	unsigned int i;

	for (i = 0; i < sizeof(deo_keymap) / sizeof(deo_keymap[0]); i++) {
		if (deo_keymap[i].xkey == keycode)
			return &deo_keymap[i];
	}
	return NULL;
}

static bool is_deo_keystroke(unsigned int keycode)
{
	if (deo_map_key(keycode)) return true;
	else return false;
}

enum deo_keystroke interpret_deo_keystroke(void)
{
	XEvent event;

	/* Loop until we get a relevent keypress */
	do {
		event = get_deo_event();
	} while (event.type != KeyPress || !is_deo_keystroke(event.xkey.keycode));

	assert(deo_map_key(event.xkey.keycode));

	return deo_map_key(event.xkey.keycode)->evacs_key;	
}





