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

/* Prompts functions for Data Entry */
#include "prompts.h"
#include <voting_client/image.h>

/* SIPL 2011-06-07: Changed DATA_ENTRY_IMAGE_BASE to 
   "/images.1152/data_entry/" to ensure that 
   the data entry client ballot screen always gets
   the 1152x864 images.
#define DATA_ENTRY_IMAGE_BASE "/images/data_entry/"
*/
#define DATA_ENTRY_IMAGE_BASE "/images.1152/data_entry/"

/* Get the finish prompt image (do *not* free it). */
extern struct image *get_finish_prompt(void)
{
	struct image *image;

	image = get_image(DATA_ENTRY_IMAGE_BASE "finish.png", false);
	if (!image)
		bailout("Could not fetch finish.png image!\n");

	return image;
}

/* Get the cancel prompt image (do *not* free it). */
extern struct image *get_cancel_prompt(void)
{
	struct image *image;

	image = get_image(DATA_ENTRY_IMAGE_BASE "cancel.png", false);
	if (!image)
		bailout("Could not fetch cancel.png image!\n");

	return image;
}
