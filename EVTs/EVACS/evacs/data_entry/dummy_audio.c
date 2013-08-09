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

/* Dummy implementation of audio: does nothing */
#include <stdlib.h>
#include <voting_client/audio.h>

/* Initialize the audio */
void audio_init(void)
{
}

void audio_shutdown(void)
{
}

/* Retrieve an audio sample (do not free) */
struct audio *get_audio(const char *fmt, ...)
{
	return NULL;
}

/* Play an audio sample once */
void play_audio(bool interrupt, struct audio *audio)
{
}

/* Play an audio sample in a loop */
void play_audio_loop(bool interrupt, struct audio *audio)
{
}

/* Play these samples in a loop with a pause after them */
void play_multiaudio_loop(bool interrupt,
			  unsigned int num_samples,
			  struct audio *audio[num_samples])
{
}

/* Play a pause */
void play_pause(bool interrupt)
{
}
