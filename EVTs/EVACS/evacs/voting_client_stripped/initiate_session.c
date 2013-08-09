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

#include <common/language.h>
#include <stdbool.h>
#include <stdlib.h>
#include <common/barcode.h>
#include "image.h"
#include "message.h"
#include "voting_client.h"
#include "initiate_session.h"

/* Language coordinates */
struct coordinates 
{
	unsigned int x;
	unsigned int y;
};
static struct coordinates language_position[NUM_OF_LANGUAGES];

/* DDS3.2.2: Update Language */
static void update_language(unsigned int new_language)
{
	unsigned int old_language;
	struct image *old_lang_image, *language_image, *highlighted, 
		*select_image;
    
	/* paste unhighlighted old image on right hand side of screen 
	   (languages are arrayed downwards in numerical order        */
	old_language = get_language();  
	old_lang_image = get_message(old_language,MSG_LANGUAGE_NAME);
	paste_image(language_position[old_language].x,
		    language_position[old_language].y,
		    old_lang_image);                       
    
	/* paste highlighted image of new language on screen */
	language_image = get_message(new_language,MSG_LANGUAGE_NAME);
	highlighted = highlight_image(language_image);
	paste_image(language_position[new_language].x,
		    language_position[new_language].y,
		    highlighted);

	select_image = get_message(new_language, 
				   MSG_SWIPE_BARCODE_TO_BEGIN);
	paste_image(0,0,select_image);
    
	/* save the new language */
	set_language(new_language); 
}

/* SIPL 2011: Commented out the following function, because it is never used. */
/* DDS3.2.2: Format Welcome Screen */
/* static void welcome_screen(void) */
/* { */
/* 	unsigned int y, i; */
/* 	unsigned int init_language = 0; */
/* 	struct image *language_image[NUM_OF_LANGUAGES],  */
/* 		*instruction_image[NUM_OF_LANGUAGES], *begin_image; */

/* 	/\* Get all multilingual images *\/ */
/* 	for (i = 0; i < NUM_OF_LANGUAGES; i++) { */
/* //fprintf(stderr, "getting Language image for %d\n", i); */
/* 		language_image[i] = get_message(i, MSG_LANGUAGE_NAME); */
/* //fprintf(stderr, "getting UP-down image for %d\n", i); */
/* 		instruction_image[i] = get_message(i, MSG_PRESS_UP_DOWN_TO_SELECT_LANGUAGE); */
/* 	} */

/* //fprintf(stderr, " drawing background\n"); */
/* 	/\* Draw background *\/ */
/* 	paste_image(0, 0, get_message(init_language, MSG_BACKGROUND)); */

/* sleep(5); */

/* 	/\* Paste top image *\/ */
/* 	begin_image = get_message(init_language, MSG_SWIPE_BARCODE_TO_BEGIN); */
/* 	paste_image(0, 0, begin_image); */
/* 	y = image_height(begin_image); */

/* //fprintf(stderr, " drawing screen\n"); */
/* 	/\* Lay them out down the screen *\/ */
/* 	for (i = 0; i < NUM_OF_LANGUAGES; i++) { */
/* 		unsigned int x, width; */

/* 		/\* Total width *\/ */
/* 		width = image_width(language_image[i]) */
/* 			+ image_width(instruction_image[i]); */
/* 		/\* Halfway across *\/ */
/* 		x = get_screen_width() / 2 - width / 2; */
/* 		paste_image(x, y, instruction_image[i]); */

/* 		/\* This is where the actual language image sits *\/ */
/* 		language_position[i].x = x + image_width(instruction_image[i]); */
/* 		language_position[i].y = y; */
/* 		paste_image(language_position[i].x, */
/* 			    language_position[i].y, */
/* 			    language_image[i]); */

/* 		/\* Move down *\/ */
/* 		y += image_height(instruction_image[i]); */
/* 	} */

/* //fprintf(stderr, " Init'ing the language \n"); */
/* 	/\* Update the current language to be English *\/ */
/* 	update_language(init_language); */
/* } */



/* DDS3.2.2: Initiate Session */
void init_session(void)
{
	update_language(0);
	set_language(0);
}
