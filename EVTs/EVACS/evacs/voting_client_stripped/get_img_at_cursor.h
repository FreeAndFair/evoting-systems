#ifndef _GET_IMG_AT_CURSOR_H
#define _GET_IMG_AT_CURSOR_H
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
struct image;
struct cursor;
struct audio;

struct image_set
{
	/* Either group image is non-NULL... */
	struct image *group;
	/* ...or preference number image and candidate image are non-NULL. */
	struct image *prefnumber, *candidate;
};

struct audio_set
{
	/* Either this is non-NULL */
	struct audio *group_audio;
	/* Or these are to be used */
	struct audio *candidate_audio[3];
};

extern struct image_set get_img_at_cursor(const struct cursor *cursor);
extern struct audio_set get_audio_at_cursor(const struct cursor *cursor);
#endif /*_GET_IMG_AT_CURSOR_H*/

