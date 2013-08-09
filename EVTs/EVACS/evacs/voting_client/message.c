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
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <common/http.h>
#include <common/language.h>
#include "voting_client.h"
#include "message.h"
#include "initiate_session.h"
#include "input.h"
#include "audio.h"

static struct image *get_message_mayfail(unsigned int language,
					 enum message msg)
{
	char url[strlen(IMAGE_BASE)
		+ INT_CHARS + 1 + INT_CHARS + sizeof(".png")];
	bool need_highlight;

	assert(language < NUM_OF_LANGUAGES && msg < MSG_MAX);

	/* These are the only images which need highlighting
           (optimization to avoid highlighting full screen images) */
	if (msg == MSG_LANGUAGE_NAME
	    || msg == MSG_YES
	    || msg == MSG_NO)
		need_highlight = true;
	else
		need_highlight = false;

	/* Now ask server */
	sprintf(url, "%s%u/%u.png", IMAGE_BASE, language, (unsigned int)msg);
	return get_image(url, need_highlight);
}

/* DDS3.2.14: Get Message */
struct image *get_message(unsigned int language, enum message msg)
{
	struct image *message;

	if((message = get_message_mayfail(language,msg))==NULL){
		display_error(ERR_SERVER_UNREACHABLE);
	}	

	return(message);
}

/* This is called directly to display error numbers */
static struct image *get_preference_image_mayfail(unsigned int ecode,
						  unsigned int number)
{
	char url[strlen(NUMBER_BASE)
		+ INT_CHARS + 1 + INT_CHARS + sizeof(".png")];

	assert(number <= PREFNUM_MAX);

	/* Ask server. */
	sprintf(url, NUMBER_BASE "%u.png", ecode, number);
	return get_image(url, true);
}

/* DDS3.2.14: Get Preference Number Image */
struct image *get_preference_image(unsigned int ecode, unsigned int number)
{
	struct image *preference;

	if((preference = get_preference_image_mayfail(ecode,number))==NULL){
		display_error(ERR_SERVER_UNREACHABLE);
	}

	return(preference);
}

/* DDS3.2.12: Get Group Image */
struct image *get_group_image(unsigned int ecode, unsigned int group_index)
{
	char url[strlen(GROUP_BASE)
		+ INT_CHARS + 1 + INT_CHARS + sizeof(".png")];
	struct image *image;

	/* Now ask server */
	sprintf(url, "%s%u/%u.png", GROUP_BASE, ecode, group_index);
	image = get_image(url, true);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}

/* DDS???: Get Candidate Image */
struct image *get_candidate_image(unsigned int ecode,
				  unsigned int group_index,
				  unsigned int dbci)
{
	char url[strlen(CANDIDATE_BASE)
		+ INT_CHARS + 1 + INT_CHARS + 1 + INT_CHARS + sizeof(".png")];
	struct image *image;

	/* Now ask server */
	sprintf(url, "%s%u/%u/%u.png", CANDIDATE_BASE, ecode, group_index,
		dbci);
	image = get_image(url, true);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}		

/* DDS3.2.8: Get Ballot Heading Image */
struct image *get_bh_image(unsigned int language,
			   const struct electorate *elec)
{
	struct image *image;
	char url[strlen(IMAGE_BASE)
		+ INT_CHARS + 1 + INT_CHARS + sizeof("heading-%u.png")];

	/* Now ask server */
	sprintf(url, "%s%u/heading-%u.png", IMAGE_BASE, language, elec->code);
	image = get_image(url, false);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}

/* Get the blank image (do *not* free it). */
struct image *get_blank_image(unsigned int ecode)
{
	char url[strlen(GROUP_BASE)
		+ INT_CHARS + 1 + sizeof("blank.png")];
	struct image *image;

	/* Now ask server */
	sprintf(url, "%s%u/blank.png", GROUP_BASE, ecode);
	image = get_image(url, true);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}

/* SIPL 2011-06-28 New image for use with split groups. */
/* Get the blank image with no dividing line (do *not* free it). */
struct image *get_blank_image_no_divider(unsigned int ecode)
{
	char url[strlen(GROUP_BASE)
		+ INT_CHARS + 1 + sizeof("blank-no-borders.png")];
	struct image *image;

	/* Now ask server */
	sprintf(url, "%s%u/blank-no-borders.png", GROUP_BASE, ecode);
	image = get_image(url, true);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}

/* Get the blank image (do *not* free it). */
struct image *get_blank_group_image(unsigned int ecode)
{
	char url[strlen(GROUP_BASE)
		+ INT_CHARS + 1 + sizeof("blank-group.png")];
	struct image *image;

	/* Now ask server */
	sprintf(url, "%s%u/blank-group.png", GROUP_BASE, ecode);
	image = get_image(url, true);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}


/* DDS????: Display Error */
void display_error(enum error err)
{
	unsigned int language;
	struct image *bgimage;

	language = get_language();

	/* Draw background if we can, otherwise clear screen */
	bgimage = get_message_mayfail(language, MSG_BACKGROUND);
	if (bgimage) paste_image(0, 0, bgimage);
	else clear_screen();

	/* Message to tell them */
	play_audio(true, get_audio("error.raw"));

	/* Use electorate "1" here for the numbers. */
	draw_error(get_message_mayfail(language, MSG_ERROR),
		   get_preference_image_mayfail(1, (unsigned int)err),
		   err);

	/* Loop until reset. */
	wait_for_reset();
}

/* DDS????: Get Candidate With Group Image */
struct image *get_cand_with_group_img(unsigned int ecode,
				      unsigned int group_index,
				      unsigned int dbci)
{
	char url[strlen(CANDIDATE_BASE)
		+ INT_CHARS + 1 + INT_CHARS + 1 + INT_CHARS
		+ sizeof("-with-group.png")];
	struct image *image;

	/* Now ask server */
	sprintf(url, "%s%u/%u/%u-with-group.png",
		CANDIDATE_BASE, ecode, group_index, dbci);
	image = get_image(url, true);
	if (!image)
		display_error(ERR_SERVER_UNREACHABLE);

	return image;
}		
