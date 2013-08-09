#ifndef _CHILD_AUDIO_H
#define _CHILD_AUDIO_H
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

/* Commands are passed down pipe, followed by an optional size and
   audio sample */
enum command {
	AUDIO_STOP,
	AUDIO_PLAY,
	AUDIO_LOOP,
	AUDIO_PAUSE,
	AUDIO_EXIT,
	AUDIO_VOLUME_UP,
	AUDIO_VOLUME_DOWN,
	AUDIO_VOLUME_RESET
};

extern void child_audio(int pipe_to_parent, int pipe_from_parent);
#endif /*_CHILD_AUDIO_H*/
