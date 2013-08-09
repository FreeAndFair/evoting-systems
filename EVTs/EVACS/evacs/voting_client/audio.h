#ifndef _AUDIO_H
#define _AUDIO_H
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
/* Audio routines for EVACS */
#include <stdbool.h>

struct audio;

/* Initialize the audio */
extern void audio_init(void);
extern void audio_shutdown(void);

/* Retrieve an audio sample (do not free it) */
extern struct audio *get_audio(const char *fmt, ...)
__attribute__((format (printf,1,2)));

/* Play an audio sample once (set interrupt to true to stop anything
   currently playing, otherwise it will play after that). */
extern void play_audio(bool interrupt, struct audio *);

/* Play an audio sample in a loop with a pause after it */
extern void play_audio_loop(bool interrupt, struct audio *);

/* Play these samples in a loop with a pause after them */
extern void play_multiaudio_loop(bool interrupt, 
				 unsigned int num_samples,
				 struct audio *audio[num_samples]);

/* Play a pause */
extern void play_pause(bool interrupt);

/* Increase the volume */
extern void increase_volume(void);

/* Decrease the volume */
extern void decrease_volume(void);

/* Reset the volume to its default level */
extern void reset_volume(void);

#endif /*_AUDIO_H*/
