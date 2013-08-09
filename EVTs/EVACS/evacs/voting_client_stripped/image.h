#ifndef _IMAGE_H
#define _IMAGE_H
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

/* Image/image-related functions for voting client */
#include <stdbool.h>
#include <X11/Xlib.h>
#include "voting_client.h"

/* There is a struct image.  It is opaque. */
struct image;

/* Initialise the graphics display: return true if OK. */
/* Set upside_down to true if this should be displayed inverted */
extern bool initialise_display(int screen_width, int screen_height, bool is_upside_down);

/* Return the screen width in pixels */
extern unsigned int get_screen_width(void);

/* Return the screen height in pixels */
extern unsigned int get_screen_height(void);

/* Draw an image on the screen (0,0 is top left). */
extern void paste_image(unsigned x, unsigned y, struct image *image);

/* Given a URL, return the image or NULL for error. */
extern struct image *get_image(const char *url, bool need_highlight);

/* Given an image, get the height or width */
extern unsigned int image_height(struct image *image);
extern unsigned int image_width(struct image *image);

/* Return a highlighted image. */
extern struct image *highlight_image(struct image *oldimage);

/* Draw an error on the screen (first two may be null if server fails). */
extern void draw_error(struct image *error,
		       struct image *number,
		       enum error err);

/* Clear the screen to all white */
extern bool clear_screen(void);

/* Turn off display */
extern void close_display(void);

/* For input.c to get the X display */
extern Display *get_display(void);
#endif /*_IMAGE_H*/
