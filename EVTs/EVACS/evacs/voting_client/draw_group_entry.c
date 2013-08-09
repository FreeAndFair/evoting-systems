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

#include <common/ballot_contents.h>
#include <common/voter_electorate.h>
#include "draw_group_entry.h"
#include "message.h"
#include "verify_barcode.h"
#include "image.h"
#include "get_img_at_cursor.h"
#include "initiate_session.h"
#include "voting_client.h"
#include "audio.h"

struct coordinates 
{
	unsigned int x;
	unsigned int y;
};

/* DDS3.2.12: Get Group Width */
static unsigned int get_group_width(const struct electorate *voter_electorate)
{
	struct image *image;

	/* SIPL 2011-06-28 This was:
	   image = get_group_image(voter_electorate->code,1);
	   But to support split groups, this particular image
	   may not be one physical column wide.  So instead,
	   find an image which must still be one physical column wide,
	   e.g., the blank image. */

	image = get_blank_image(voter_electorate->code);
	return image_width(image);
}

static unsigned int get_group_h_height(const struct electorate 
				       *voter_electorate)
{
	struct image *image;

	image = get_group_image(voter_electorate->code,1);

	return image_height(image);
}


/* DDS3.2.12: Get Preference Image Size */
static unsigned int get_preference_image_size(const struct electorate 
					      *voter_electorate)
{
	struct image *image;
	
	image = get_preference_image(voter_electorate->code, 0);
	
	return image_height(image);
}


/* DDS3.2.12: Get Ballot Heading Height */
static unsigned int get_ballot_h_height(const struct electorate 
					*voter_electorate)
{
	struct image *ballot_h_image;
	
	ballot_h_image = get_bh_image(get_language(), voter_electorate);

	return image_height(ballot_h_image);
}


/* SIPL 2011-07-11 Removed "static" from the definition,
   as this is now called from main_screen.c. Renamed. */
/* Calculate how many grid blocks fit across the screen */
unsigned int get_grid_blocks_across(const struct electorate *voter_elec)
{
	unsigned int group_width;

	group_width = get_group_width(voter_elec);

	/* We want to round UP, not DOWN. */
	/* NOOOO, we want to round down!!! or else we get a partial group */
	return (get_screen_width()) / group_width; 
}

/* How tall is a group? */
static unsigned int get_group_height(const struct electorate *voter_electorate)
{
	return get_group_h_height(voter_electorate)
		+ (voter_electorate->num_seats
		   * get_preference_image_size(voter_electorate));
}

/* DDS3.2.12: Calculate Cursor Coordinates */
/* SIPL 2011-06-28 Take the possibility of split groups into account. */
static struct coordinates calc_curs_coord(unsigned int group_index, 
					   int candidate_index)
{
	struct coordinates coordinates;
	const struct electorate *voter_electorate;
	unsigned int group_height, num_columns;
	/* SIPL 2011-06-28 Calculate the physical column and grid block
	   based on group_index and the ballot data. */
	unsigned int physical_column;
	unsigned int grid_block;

	/* SIPL 2011-06-28 Need the ballot to work out where
	   the split groups are. */
	struct ballot_contents *bc = get_ballot_contents();

	physical_column = bc->map_group_to_physical_column[group_index];
	/* candidate_index may be -1, to indicate the group heading.
	   It is an error to compare this with the unsigned values
	   in the num_candidates_in_physical_column[] array without
	   the cast.
	*/
	while (candidate_index >=
	       (int)bc->num_candidates_in_physical_column[physical_column]) {
		candidate_index = candidate_index -
			bc->num_candidates_in_physical_column[physical_column];
		physical_column++;
	}

	grid_block = bc->map_physical_column_to_grid_block[physical_column];
	voter_electorate = get_voter_electorate();
	group_height = get_group_height(voter_electorate);
	num_columns = get_grid_blocks_across(voter_electorate);

	/* First calculate coordinates of group */
	/* SIPL 2011-06-28 Now use grid_block instead of group_index. */
	coordinates.x = (grid_block % num_columns)
		* get_group_width(voter_electorate);
	coordinates.y = get_ballot_h_height(voter_electorate)
		+ (grid_block / num_columns) * group_height;

	/* Now calculate coordinates of this candidate */
	/* SIPL 2011-06-28 . . . or group. */
	coordinates.y += (candidate_index + 1)
		* get_preference_image_size(voter_electorate);

	return coordinates;
}

/* DDS3.2.12: Get Cursor Coordinates */
static struct coordinates get_cursor_coordinates(struct cursor cursor)
{
	struct coordinates coordinates;
	
	coordinates = calc_curs_coord(cursor.group_index, 
				      cursor.screen_candidate_index);
	
	return coordinates;
}

/* SIPL 2011-06-28 Do the same as calc_curs_coord, but take
   the grid block as the first parameter.
   This is needed for calculating the position of blank entries.
*/
static struct coordinates calc_curs_coord_grid_block(
					unsigned int grid_block,
					int candidate_index)
{
	struct coordinates coordinates;
	const struct electorate *voter_electorate;
	unsigned int group_height, num_columns;

	voter_electorate = get_voter_electorate();
	group_height = get_group_height(voter_electorate);
	num_columns = get_grid_blocks_across(voter_electorate);

	coordinates.x = (grid_block % num_columns)
		* get_group_width(voter_electorate);
	coordinates.y = get_ballot_h_height(voter_electorate)
		+ (grid_block / num_columns) * group_height;

	/* Now calculate coordinates of this blank entry. */
	coordinates.y += (candidate_index + 1)
		* get_preference_image_size(voter_electorate);

	return coordinates;
}


/* DDS3.2.12: Draw Group Entry */
void draw_group_entry(struct cursor cursor, enum HlFlag highlight,
		      bool interrupt)
{
	struct image_set set;
	struct image *image, *highlighted;
	struct coordinates coordinates;
	unsigned int pref_size;
	struct audio_set audio = { NULL, { NULL, NULL, NULL } };

	/* We play audio only if highlighted */
	if (highlight)
		audio = get_audio_at_cursor(&cursor);

	set = get_img_at_cursor(&cursor);
	
	coordinates = get_cursor_coordinates(cursor);

	/* set contains either a group heading image or a candidate 
	   and pref_box image */
	if (set.group) {
		image = set.group;
		if (highlight) {
			highlighted = highlight_image(image);
			paste_image(coordinates.x, coordinates.y, highlighted);
			play_audio_loop(interrupt, audio.group_audio);
		}
		else {
			paste_image(coordinates.x, coordinates.y, image);
		}
	}
	else {
		/* set contains candidate and pref_box images */
		image = set.candidate;
		pref_size = image_width(set.prefnumber);
		paste_image(coordinates.x, coordinates.y, set.prefnumber);
		if (highlight) {
			highlighted = highlight_image(image);
			paste_image(coordinates.x + pref_size, coordinates.y, 
				    highlighted);

			/* Audio for this candidate */
			play_multiaudio_loop(interrupt, 3,
					     audio.candidate_audio);
		} else {
			paste_image(coordinates.x + pref_size, coordinates.y, 
				    image);
		}
				   
	}
}

/* SIPL 2011-06-28 Because there can now be split groups,
   need to be able to draw blank entries in the "middle"
   of a group.  This version of the function is no longer able to cope. */
// /* Draw a blank entry */
// void draw_blank_entry(unsigned int group_index,
// 		      int screen_index)
// {
// 	struct image *blank;
// 	struct cursor cursor;
// 	struct coordinates coords;
// 
// 	/* Create a dummy cursor for this position */
// 	cursor.group_index = group_index;
// 	cursor.screen_candidate_index = screen_index;
// 	/* Convert to screen coordinates */
// 	coords = get_cursor_coordinates(cursor);
// 
// 	/* Get the blank image for this electorate, and paste it */
// 	blank = get_blank_image(get_voter_electorate()->code);
// 	paste_image(coords.x, coords.y, blank);
// }

/* SIPL 2011-06-28 Modification of draw_blank_entry that
   takes a grid block as the first parameter. */
/* Draw a blank entry */
void draw_blank_entry_grid_block(unsigned int grid_block,
				 int screen_index)
{
	struct image *blank;
	struct coordinates coords;

	/* Create a dummy cursor for this position */
	/* Convert to screen coordinates */
	coords = calc_curs_coord_grid_block(grid_block,
					    screen_index);
	/* Get the blank image for this electorate, and paste it */
	blank = get_blank_image(get_voter_electorate()->code);
	paste_image(coords.x, coords.y, blank);
}

/* SIPL 2011-06-28 As per draw_blank_entry_grid_block but
   using the completely blank image, without the dividing line at
   the right-hand side. */
void draw_blank_entry_no_divider_grid_block(unsigned int grid_block,
					    int screen_index)
{
	struct image *blank;
	struct coordinates coords;

	/* Create a dummy cursor for this position */
	/* Convert to screen coordinates */
	coords = calc_curs_coord_grid_block(grid_block,
					    screen_index);
	/* Get the blank image for this electorate, and paste it */
	blank = get_blank_image_no_divider(get_voter_electorate()->code);
	paste_image(coords.x, coords.y, blank);
}

/* Draw a blank group entry */
void draw_blank_group_entry(unsigned int group_index)
{
	struct image *blank;
	struct cursor cursor;
	struct coordinates coords;

	/* Create a dummy cursor for this position */
	cursor.group_index = group_index;
	cursor.screen_candidate_index = -1;
	/* Convert to screen coordinates */
	coords = get_cursor_coordinates(cursor);

	/* Get the blank image for this electorate, and paste it */
	blank = get_blank_group_image(get_voter_electorate()->code);
	paste_image(coords.x, coords.y, blank);
}

/* SIPL 2011-06-29 New function taking a grid block as parameter. */
/* Draw a blank group entry */
void draw_blank_group_entry_grid_block(unsigned int grid_block)
{
	struct image *blank;
	struct coordinates coords;

	/* Use -1 to get the position of the group heading. */
	coords = calc_curs_coord_grid_block(grid_block, -1);

	/* Get the blank image for this electorate, and paste it */
	blank = get_blank_group_image(get_voter_electorate()->code);
	paste_image(coords.x, coords.y, blank);
}


/* SIPL 2011-06-29 Renamed. */
/* How many grid blocks *could* fit on the screen? */
unsigned int grid_blocks_possible(void)
{
	unsigned int num_columns, column_height, num_rows;
	const struct electorate *voter_electorate;

	voter_electorate = get_voter_electorate();
	num_columns = get_grid_blocks_across(voter_electorate);
	column_height = get_group_height(voter_electorate);

	/* We want to round UP, not down */
	num_rows = (get_screen_height() - get_ballot_h_height(voter_electorate)
		    + column_height-1) / column_height;

	return num_rows * num_columns;
}
