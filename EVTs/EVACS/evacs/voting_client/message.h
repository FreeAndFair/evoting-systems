#ifndef _MESSAGE_H
#define _MESSAGE_H
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

/* Message/image-related functions for voting client */
#include <stdbool.h>
#include "image.h"
#include "voting_client.h"

enum message
{
	MSG_BACKGROUND = 0,
	MSG_PRESS_UP_DOWN_TO_SELECT_LANGUAGE = 1,
	MSG_SWIPE_BARCODE_TO_BEGIN = 2,
	MSG_ERROR = 4,
	MSG_START_AGAIN_PROMPT = 5,
	MSG_YES = 6,
	MSG_NO = 7,
	MSG_CHECK_YOUR_VOTE = 8,
	MSG_SWIPE_BARCODE_TO_CONFIRM = 9,
	MSG_PRESS_SELECT_TO_HIDE = 10,
	MSG_NO_CANDIDATES_SELECTED = 11,
	MSG_YOUR_VOTE_WILL_BE_INFORMAL = 12,
	MSG_YOUR_VOTE_HAS_BEEN_HIDDEN = 13,
	MSG_ACKNOWLEDGEMENT = 14,
	MSG_LANGUAGE_NAME = 17,
	MSG_MAX = 18
};

/* Get a message image (do *not* free it). */
extern struct image *get_message(unsigned int language,
				 enum message msg);

/* Get a preference number image (do *not* free it). */
extern struct image *get_preference_image(unsigned int ecode,
					  unsigned int number);

/* Get a group image (do *not* free it). */
extern struct image *get_group_image(unsigned int ecode,
				     unsigned int group_index);

/* Get a candidate image (do *not* free it). */
extern struct image *get_candidate_image(unsigned int ecode,
					 unsigned int group_index,
					 unsigned int dbci);

extern struct image *get_cand_with_group_img(unsigned int ecode,
					     unsigned int group_index,
					     unsigned int dbci);

/* Get the blank image (do *not* free it). */
extern struct image *get_blank_image(unsigned int ecode);

/* SIPL 2011-06-28 New image for use with split groups. */
/* Get the blank image with no dividing line (do *not* free it). */
extern struct image *get_blank_image_no_divider(unsigned int ecode);

/* Get the blank group image (do *not* free it). */
extern struct image *get_blank_group_image(unsigned int ecode);

/* Get Ballot Heading Image */
extern struct image *get_bh_image(unsigned int language,
				  const struct electorate *elec);

/* Display the error screen */
extern void display_error(enum error err) /*__attribute__((noreturn))*/;
#endif /*_MESSAGE_H*/
