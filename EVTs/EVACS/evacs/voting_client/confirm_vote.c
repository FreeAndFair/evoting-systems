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
#include <common/barcode.h>
#include <common/voter_electorate.h>
#include "input.h"
#include "confirm_vote.h"
#include "verify_barcode.h"
#include "vote_in_progress.h"
#include "message.h"
#include "commit.h"
#include "audio.h"

static void draw_candidates(unsigned int top,
			    const struct preference_set *vote)
{
	unsigned int i, x, y;
	struct image *candimg, *prefimg;
	const struct electorate *elec;

	x = 0;
	y = top;
	elec = get_voter_electorate();

	for (i = 0; i < vote->num_preferences; i++) {
		/* Fetch preference image for this candidate (1-based). */
		prefimg = get_preference_image(elec->code, i+1);
		/* Fetch candidate image */
		candimg = get_cand_with_group_img(elec->code,
						  vote->candidates[i]
						  .group_index,
						  vote->candidates[i]
						  .db_candidate_index);

		/* Are we going to go off the screen? */
		if (y + image_height(prefimg) >= get_screen_height()) {
			/* Move across one column */
			x += image_width(prefimg) + image_width(candimg);
			y = top;
		}

		/* Paste them side-by-side on the screen */
		paste_image(x, y, prefimg);
		paste_image(x + image_width(prefimg), y, candimg);

		/* Move down the screen (both images are same height) */
		y += image_height(prefimg);
	}
}

/* Draw the informal screen */
static void format_informal_screen(unsigned int language)
{
	unsigned int ypos;
	struct image *no_cands, *informal, *confirm, *hide;

	/* Screen consists of these four images */
	no_cands = get_message(language, MSG_NO_CANDIDATES_SELECTED);
	informal = get_message(language, MSG_YOUR_VOTE_WILL_BE_INFORMAL);
	confirm = get_message(language, MSG_SWIPE_BARCODE_TO_CONFIRM);
	hide = get_message(language, MSG_PRESS_SELECT_TO_HIDE);

	/* Start at centre of the screen, minus half their heights. */
	ypos = (get_screen_height()
		- image_height(no_cands)
		- image_height(informal)
		- image_height(confirm)
		- image_height(hide))/2;

	/* Paste them one under the other */
	paste_image(0, ypos, no_cands);
	ypos += image_height(no_cands);
	paste_image(0, ypos, informal);
	ypos += image_height(informal);
	paste_image(0, ypos, confirm);
	ypos += image_height(confirm);
	paste_image(0, ypos, hide);

	play_audio_loop(true, get_audio("informal.raw"));
}

/* Play audio messages */
static void play_candidates_in_loop(const struct electorate *elec,
				    const struct preference_set *vip)
{
	unsigned int i;
	struct audio *audio[1 + vip->num_preferences*3 + 1];

	/* Start of spiel... */
	audio[0] = get_audio("formal.raw");
	for (i = 0; i < vip->num_preferences; i++) {
		/* Preference number, candidate name, group name */
		audio[1 + i*3] = get_audio("numbers/%u.raw", i+1);
		audio[1 + i*3 + 1]
			= get_audio("electorates/%u/%u/%u.raw",
				    elec->code,
				    vip->candidates[i].group_index,
				    vip->candidates[i].db_candidate_index);
		audio[1 + i*3+2] 
		        = get_audio("electorates/%u/%u.raw",
				    elec->code,
				    vip->candidates[i].group_index);
	}
	/* ... end of spiel */
	audio[1 + i*3] = get_audio("formal2.raw");

	play_multiaudio_loop(true, 1 + vip->num_preferences*3 + 1, audio);
}

/* DDS3.2.24: Display Confirmation Screen */
static void format_confirm_screen(unsigned int language)
{
	const struct preference_set *vote;
	struct image *img;
	unsigned int ypos = 0;

	/* Figure out what they voted */
	vote = get_vote_in_progress();

	/* Draw background */
	paste_image(0, 0, get_message(language, MSG_BACKGROUND));

	/* Informal screen looks different */
	if (vote->num_preferences == 0) {
		format_informal_screen(language);
		return;
	}

	/* Formal vote: paste messages at top, candidates underneath. */
	img = get_message(language, MSG_CHECK_YOUR_VOTE);
	paste_image(0, ypos, img);
	ypos += image_height(img);
	img = get_message(language, MSG_SWIPE_BARCODE_TO_CONFIRM);
	paste_image(0, ypos, img);
	ypos += image_height(img);
	img = get_message(language, MSG_PRESS_SELECT_TO_HIDE);
	paste_image(0, ypos, img);
	ypos += image_height(img);
	draw_candidates(ypos, vote);

	/* Play audio messages */
	play_candidates_in_loop(get_voter_electorate(), vote);
}

/* DDS3.2.22: Formate Hidden Vote Screen */
static void format_hidden_vote_screen(unsigned int language)
{
	unsigned int ypos;
	struct image *hidden, *confirm;

	/* Draw background */
	paste_image(0, 0, get_message(language, MSG_BACKGROUND));

	hidden = get_message(language, MSG_YOUR_VOTE_HAS_BEEN_HIDDEN);
	confirm = get_message(language, MSG_SWIPE_BARCODE_TO_CONFIRM);

	/* Draw images in centre of screen */
	ypos = (get_screen_height()
		- image_height(hidden)
		- image_height(confirm))/2;
	paste_image(0, ypos, hidden);
	ypos += image_height(hidden);
	paste_image(0, ypos, confirm);
	
	/* Play audio message */
	play_audio_loop(true, get_audio("hidden.raw"));

}

/* DDS3.2.22: Confirm and Commit Vote */
bool confirm_and_commit_vote(unsigned int language)
{
	struct barcode bc;
	
	format_confirm_screen(language);

	for (;;) {
		switch (get_keystroke_or_barcode(&bc)) {
		case INPUT_SELECT:
			/* Hide vote */
			format_hidden_vote_screen(language);
			break;
		case INPUT_UNDO:
			/* Continue voting */
			return true;
			break;
		case INPUT_VOLUME_UP:
			increase_volume();
			break;
		case INPUT_VOLUME_DOWN:
			decrease_volume();
			break;
		case INPUT_BARCODE:
			/* If barcode OK, commit the vote */
			if (verify_barcode(&bc)) {
				commit_vote(&bc);
				/* Do not continue voting */
				return false;
			}
			break;

		default:
			/* Ignore other keys */
			break;
		}
	}
}
