/* This file is (C) copyright 2001-2008 Software Improvements, Pty Ltd. */

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
#include <fcntl.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/ioctl.h>
#include <sys/time.h>
#include <sys/types.h>
#include <linux/soundcard.h>
#include "child_audio.h"

/* How many ms do we keep in audio buffer? */
#define AUDIO_LOW_WATERMARK 50
#define AUDIO_HIGH_WATERMARK (AUDIO_LOW_WATERMARK + 50)

/* Sleep time in ms */
#define SLEEP_TIME 2000

#define AUDIO_INPUT_RATE 11025

/* 2008-08-15 Changes to volume settings made
   because of different sound card. */
#define MIN_VOLUME 0
#define MAX_VOLUME 80
#define VOLUME_INCREMENT 5
#define DEFAULT_VOLUME 50

/* 2008-08-15 PCM level will be set permanently at this level;
   only the master volume will be adjusted. */
#define DEFAULT_PCM_LEVEL 100

typedef struct stereovolume
{
	unsigned char left;
	unsigned char right;
} StereoVolume;

/* The rate the audio output is actually set to */
static unsigned int rate;

/* The fragment size for audio writes */
static unsigned int fragsize;

/* The number of bytes available at the start */
static unsigned int bytes_total;

/* We can't use global bailout, as voting client must not be linked
   with evacs.c */
static void bailout(const char *fmt, ...) __attribute__((noreturn));

static void bailout(const char *fmt, ...)
{
	va_list arglist;

	va_start(arglist,fmt);
	fprintf(stderr,"FATAL: ");
	vfprintf(stderr,fmt,arglist);
	va_end(arglist);
  
	exit(1);
}

/* Linked list of audio to play */
struct play_list
{
	struct play_list *next;

	/* Mode for this element */
	enum command command;
	/* The actual audio data */
	char *buffer;
	/* The size of the audio data in bytes */
	unsigned int bufsize;
};

static int open_audiodev(const char *device)
{
	int fd;
	int channels = 2;
	int format = AFMT_S16_LE;
	audio_buf_info info;
	int setting = (8 << 16) | 12;

	fd = open(device, O_WRONLY, 0);
	if (fd < 0) bailout("Error opening audio: %s\n", strerror(errno));

	if (ioctl(fd, SNDCTL_DSP_SETFRAGMENT, &setting) != 0)
	  bailout("Error setting fragment size!: %s\n", strerror(errno));

	/* Try for matching rate */
	rate = AUDIO_INPUT_RATE;

	if (ioctl(fd, SNDCTL_DSP_CHANNELS, &channels) != 0
	    || ioctl(fd, SNDCTL_DSP_SETFMT, &format) != 0
	    || ioctl(fd, SNDCTL_DSP_SPEED, &rate) != 0) 
		bailout("Error setting up audio: %s\n", strerror(errno));

	if (ioctl(fd, SNDCTL_DSP_GETOSPACE, &info) != 0)
		bailout("Could not get output space: %s\n", strerror(errno));
	fragsize = info.fragsize;
	bytes_total = info.bytes;

	/* We must be able to get the high water mark into the buffer! */
	if (info.fragsize * info.fragments 
	    < AUDIO_HIGH_WATERMARK * rate * 2 * 2 / 1000)
		bailout("High water mark too high!\n");

	return fd;
}

/* Append the sample to the list given */
static struct play_list *read_sample(int fd,
				     enum command cmd,
				     struct play_list *head)
{
	int res;
	unsigned int done;
	struct play_list *list;

	/* Allocate list element */
	list = malloc(sizeof(*list));
	list->command = cmd;
	list->next = NULL;
	
	/* Place in list if possible, or we are a new one. */
	if (head) {
		struct play_list *end = head;
		while (end->next) {
			end = end->next;
		}
		end->next = list;
	} else {
		head = list;
	}

	/* Read sample size first */
	if (read(fd, &list->bufsize, sizeof(list->bufsize))
	    != sizeof(list->bufsize))
		bailout("Error reading sample size: %s\n", strerror(errno));

	list->buffer = malloc(list->bufsize);
	done = 0;

	/* Read in a loop until all done */
	while (done < list->bufsize) {
		res = read(fd, list->buffer+done, list->bufsize - done);
		if (res <= 0) 
			bailout("Error reading %u bytes of sample: %s\n", 
				list->bufsize - done, strerror(errno));

		done += res;
	}

	/* Truncate so it's an exact fragment length */
	list->bufsize = list->bufsize/fragsize * fragsize;

	return head;
}

/* Figure out how much we time is left for the audio buffer */
static unsigned int get_time_in_buffer(int audio_fd)
{
	audio_buf_info info;
	unsigned int bytes_left;

	if (ioctl(audio_fd, SNDCTL_DSP_GETOSPACE, &info) != 0)
		bailout("Could not get output space: %s\n", strerror(errno));

	/* i810 seems to get confused... */
	if (info.bytes > bytes_total) {
		char junk[32768] = { 0 };
		write(audio_fd, junk, 32768);
		ioctl(audio_fd, SNDCTL_DSP_SYNC, &info);
		usleep(50000);
		ioctl(audio_fd, SNDCTL_DSP_GETOSPACE, &info);
	
	}
	/* How many bytes are left in the buffer? */
	bytes_left = bytes_total - info.bytes;

	/* 16-bit stereo at the given rate */
	return bytes_left / 2 / 2 * 1000 / rate;
}

/* Feed some bytes to the audio system: return bytes used. */
static unsigned int feed_sample(int audio_fd, 
				unsigned int ms_to_fill,
				char *buffer,
				unsigned int size)
{
	int16_t *outbuf, *inbuf;
	unsigned int i;

	inbuf = (int16_t *)buffer;

	/* Only use enough bytes to fill the ms required */
	if (size > ms_to_fill * AUDIO_INPUT_RATE * 2 / 1000) {
		size = ms_to_fill * AUDIO_INPUT_RATE * 2 / 1000;
		/* Round up to a fragmentsize multiple */
		size = (size + fragsize-1) / fragsize * fragsize;
	}

	/* Outbuf is in *stereo* */
	outbuf = malloc(size * 2);

	/* Do rough conversion */
	for (i = 0; i < size; i += 2)
		outbuf[i] = outbuf[i+1] = inbuf[i/2];
	/* We should have plenty of space, so write should be atomic */
	if (write(audio_fd, outbuf, size*2) != size*2)
		fprintf(stderr, "warning: short write!\n");
	free(outbuf);
	return size;
}

/* Returns how much was played */
static unsigned int play_sample(int watch_fd,
				int audio_fd,
				char *buffer,
				unsigned int size)
{
	unsigned int done = 0;
	fd_set fdset;
	struct timeval tv;

	/* Sound card only accepts partial writes, so we poll between
           writes. */
	while (done != size) {
		unsigned int time_in_buffer;

		/* How many bytes do we do this time? */
		time_in_buffer = get_time_in_buffer(audio_fd);
		if (time_in_buffer < AUDIO_HIGH_WATERMARK) {
			int this_time;
			this_time = feed_sample(audio_fd, 
						AUDIO_HIGH_WATERMARK
						- time_in_buffer,
						buffer + done,
						size - done);
			done += this_time;
			/* guesstimate */
			time_in_buffer += this_time * 1000
		 		/ (2 * AUDIO_INPUT_RATE);

	}

		
		/* Sleep until we will hit low watermark */
		if (time_in_buffer > AUDIO_LOW_WATERMARK) {
			time_in_buffer -= AUDIO_LOW_WATERMARK;

			FD_ZERO(&fdset);
			FD_SET(watch_fd, &fdset);
			/* Milliseconds to microseconds */
			tv.tv_usec = (time_in_buffer % 1000) * 1000;
			tv.tv_sec = (time_in_buffer / 1000);
			/* Are we being hailed? */
			if (select(watch_fd+1, &fdset, NULL, NULL, &tv))
				break;
		}
	}

	return done;
}

/* Delete an audio sample */
static struct play_list *clear_one_play(struct play_list *list)
{
	struct play_list *tmp = list->next;

	free(list->buffer);
	free(list);
	return tmp;
}

/* Delete a list of audio samples */
static void clear_play_list(struct play_list *list)
{
	while (list)
		list = clear_one_play(list);
}

/* Play the given number is ms of pause.  Return ms slept. */
static unsigned int play_pause(int watch_fd, int audio_fd, unsigned int ms)
{
	struct timeval tv;
	fd_set fdset;

	tv.tv_usec = (ms % 1000) * 1000;
	tv.tv_sec = (ms / 1000);

	FD_ZERO(&fdset);
	FD_SET(watch_fd, &fdset);

	if (select(watch_fd+1, &fdset, NULL, NULL, &tv) == 1)
		/* Return number of ms used */
		return ms - (tv.tv_sec * 1000 + tv.tv_usec / 1000);

	/* We slept the full time */
	return ms;
}

/* Return false when we are interrupted by something in watch_fd */
static bool play_loop(int watch_fd,
		      int audio_fd,
		      char *buffer,
		      unsigned int bufsize,
		      unsigned int *upto)
{
	/* Are we still in the sample (and not into the pause?) */
	if (*upto < bufsize) {
		*upto += play_sample(watch_fd, audio_fd,
				     buffer + *upto,
				     bufsize - *upto);
		/* Were we interrupted? */
		if (*upto != bufsize)
			return false;
	}

	/* Rest of time is spent in the pause */
	*upto += play_pause(watch_fd, audio_fd, bufsize + SLEEP_TIME - *upto);
	/* Were we interrupted? */
	if (*upto != bufsize + SLEEP_TIME)
		return false;
	
	/* Ready to go again */
	*upto = 0;
	return true;
}

static struct play_list *play(int watch_fd,
			      int audio_fd,
			      struct play_list *list,
			      unsigned int *upto)
{
	while (list) {
		switch (list->command) {
		case AUDIO_LOOP:
			/* Play this in loop, with pause after */
			while (play_loop(watch_fd, audio_fd,
					 list->buffer, list->bufsize,
					 upto))
				;
			/* We were interrupted.  Leave for the moment */
			return list;
			break;

		case AUDIO_PAUSE:
			/* upto in this case represent millisecs
                           already slept */
			*upto += play_pause(watch_fd, audio_fd,
					    SLEEP_TIME - *upto);
			if (*upto != SLEEP_TIME) {
				/* We were interrupted. */
				return list;
			}

			/* We finished pause, remove from list */
			list = clear_one_play(list);
			*upto = 0;
			break;

		case AUDIO_PLAY:
			/* A single sample to play */
			if (*upto) fprintf(stderr, "Resuming %p at %u\n", 
					   list, *upto);
			*upto += play_sample(watch_fd, audio_fd,
					     list->buffer + *upto,
					     list->bufsize - *upto);
			if (*upto != list->bufsize) {
				/* We were interrupted.  Leave for the
                                   moment */
				fprintf(stderr, "Interupted %p up to %u\n", list,
					*upto);
				return list;
			}
			fprintf(stderr, "Completed %p\n", list);

			/* Finished.  Remove from list */
			list = clear_one_play(list);
			*upto = 0;
			break;

		default:
			bailout("Unknown command: %u\n", list->command);
		}
	}

	/* List finish.  Wait for new command */
	return NULL;
}

static void set_volume(int mixer_fd, int volume) {
	StereoVolume vol;

	vol.left = vol.right = volume;
	if (ioctl(mixer_fd, MIXER_WRITE(SOUND_MIXER_VOLUME), &vol)==-1) {
                /*Error! Could not set master volume*/
                fprintf(stderr, "Unable to set master volume");
        }

        /* 2008-08-15 Code to set the PCM level the same way
           was here; it has been moved to child_audio(). */
}
	
void child_audio(int pipe_to_parent, int feed)
{
	int audio_fd;
	int mixer_fd;
	enum command command;
	struct play_list *list = NULL;
	unsigned int upto = 0;
	int volume;
	StereoVolume vol; /* Used to set PCM level */

	audio_fd = open_audiodev("/dev/dsp");
	mixer_fd = open("/dev/mixer", O_WRONLY);

        /* 2008-08-15 Set PCM level to the default; it is
           no longer adjusted after this. */
        vol.left = vol.right = DEFAULT_PCM_LEVEL;
        if (ioctl(mixer_fd, MIXER_WRITE(SOUND_MIXER_PCM), &vol)==-1) {
                /*Error! Could not set pcm volume*/
                fprintf(stderr, "Unable to set PCM volume");
        }

	/* Set master volume to the default level */
	volume = DEFAULT_VOLUME;
	set_volume(mixer_fd, volume);

	/* We're setup: call home. */
	write(pipe_to_parent, "OK", 1);

	/* Read audio samples until we get a 0 (stop) */
		while (read(feed, &command, sizeof(command)) == sizeof(command)) {
		switch (command) {
		case AUDIO_STOP:
			/* Tell audio to stop playing immediately */
#if 0
			ioctl(audio_fd, SNDCTL_DSP_RESET, 0);
#endif
			clear_play_list(list);
			upto = 0;
			list = NULL;
			break;

		case AUDIO_EXIT:
			/* Finish */
			clear_play_list(list);
			close(audio_fd);
			close(pipe_to_parent);
			close(feed);
			exit(0);

		case AUDIO_VOLUME_UP:
			volume += VOLUME_INCREMENT;
			if (volume > MAX_VOLUME) {
				volume = MAX_VOLUME;
			}
			set_volume(mixer_fd, volume);
			break;

		case AUDIO_VOLUME_DOWN:
                        volume -= VOLUME_INCREMENT;
                        if (volume < MIN_VOLUME) {
                                volume = MIN_VOLUME;
                        }
			set_volume(mixer_fd, volume);
                        break;

		case AUDIO_VOLUME_RESET:
			volume = DEFAULT_VOLUME;
			set_volume(mixer_fd, volume);
			break;

		default:
			list = read_sample(feed, command, list);
			break;
		}

		/* We play the playlist until interrupted */
		list = play(feed, audio_fd, list, &upto);
	}
	exit(1);
}
