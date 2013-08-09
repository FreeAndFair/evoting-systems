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
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <common/evacs.h>
#include <common/http.h>
#include "message.h"
#include "audio.h"
#include "child_audio.h"

static pid_t child = 0;
static int pipe_to_child;

/* Simple linked list of samples (we don't have that many) */
struct audio
{
	struct audio *next;
	size_t size;
	unsigned char *sample;
	/* Name hangs off end of structure */
	char name[0];
};
static struct audio *audio_cache = NULL;

/* Initialize the audio */
void audio_init(void)
{
	int parent_to_child[2], child_to_parent[2];
	char dummy;

	assert(child == 0);
	pipe(parent_to_child);
	pipe(child_to_parent);

	child = fork();
	if (child == (pid_t)-1)
		display_error(ERR_INTERNAL);

	if (child == 0) {
		/* Child. */
		close(parent_to_child[1]);
		close(child_to_parent[0]);
		
		child_audio(child_to_parent[1], parent_to_child[0]);
	}

	/* Parent */
	close(parent_to_child[0]);
	close(child_to_parent[1]);

	/* Wait for it to start */
	alarm(5);
	if (read(child_to_parent[0], &dummy, 1) != 1) {
		alarm(0);
		display_error(ERR_INTERNAL);
	}
	alarm(0);
	close(child_to_parent[0]);

	pipe_to_child = parent_to_child[1];
}

void audio_shutdown(void)
{
	enum command command = AUDIO_EXIT;

	assert(child);
	write(pipe_to_child, &command, sizeof(command));
	waitpid(child, NULL, 0);
}

/* Retrieve an audio sample (do not free) */
struct audio *get_audio(const char *fmt, ...)
{
	char *tmp;
	char *url;
	struct audio *i;

	va_list arglist;
	assert(child);
	va_start(arglist,fmt);
	/* Allocate memory indicated by vsnprintf */
	tmp = malloc(vsnprintf(NULL, 0, fmt, arglist) + 1);
	vsprintf(tmp, fmt, arglist);
	va_end(arglist);
	url = sprintf_malloc("%s%s", AUDIO_BASE, tmp);
	free(tmp);

	for (i = audio_cache; i; i=i->next) {
		if (strcmp(i->name, url) == 0) {
			free(url);
			return i;
		}
	}

	/* Otherwise, create new cache entry. */
	i = malloc(sizeof(*i) + strlen(url)+ 1);
	if (!i) display_error(ERR_INTERNAL);
	sprintf(i->name, "%s", url);

	/* SIPL 2011: Added cast to match
	 *   defined type of sample. */
	/* i->sample = http_get(SERVER_ADDRESS, SERVER_PORT, i->name, &i->size); */
	i->sample = (unsigned char *)http_get(SERVER_ADDRESS, SERVER_PORT, i->name, &i->size);
	if (!i->sample) {
		free(i);
#if 0
		display_error(ERR_SERVER_UNREACHABLE);
#else
		return NULL;
#endif
	}

	/* Sew it into head of list */
	i->next = audio_cache;
	audio_cache = i;

	free(url);
	return i;
}

/* Write the header for this command to the child */
static void send_header(size_t size, enum command command)
{
	if (write(pipe_to_child, &command, sizeof(command)) != sizeof(command))
		display_error(ERR_INTERNAL);

	if (write(pipe_to_child, &size, sizeof(size)) != sizeof(size))
		display_error(ERR_INTERNAL);
}

/* Send the sample contents */
static void send_sample(unsigned char *sample, size_t size)
{
	unsigned int written;

	/* Feed actual sample: beware partial writes */
	written = 0;
	while (written < size) {
		int res;
		res = write(pipe_to_child, sample + written, size - written);
		if (res <= 0)
			display_error(ERR_INTERNAL);
		written += res;
	}
}

/* Actually tell the child to do something. */
static void play(unsigned char *sample, size_t size, enum command command)
{
	/* First send header */
	send_header(size, command);

	/* Now send sample */
	send_sample(sample, size);
}

/* Stop the music. */
static void play_stop(void)
{
	enum command command = AUDIO_STOP;
	write(pipe_to_child, &command, sizeof(command));
}

/* Play an audio sample once */
void play_audio(bool interrupt, struct audio *audio)
{
	if (interrupt) play_stop();
	if (audio)
		play(audio->sample, audio->size, AUDIO_PLAY);
}

/* Play an audio sample in a loop */
void play_audio_loop(bool interrupt, struct audio *audio)
{
	if (interrupt) play_stop();
	if (audio)
		play(audio->sample, audio->size, AUDIO_LOOP);
}

/* Play these samples in a loop with a pause after them */
void play_multiaudio_loop(bool interrupt,
			  unsigned int num_samples,
			  struct audio *audio[num_samples])
{
	unsigned int i;
	size_t total_size = 0;

	if (interrupt) play_stop();

	/* Figure out their total size */
	for (i = 0; i < num_samples; i++) {
		if (audio[i])
			total_size += audio[i]->size;
	}
	if (total_size == 0)
		return;

	/* Now we sent it as one giant sample */
	send_header(total_size, AUDIO_LOOP);
	for (i = 0; i < num_samples; i++)
		if (audio[i])
			send_sample(audio[i]->sample, audio[i]->size);
}

/* Play a pause */
void play_pause(bool interrupt)
{
	assert(child);
	if (interrupt) play_stop();
	play(NULL, 0, AUDIO_PAUSE);
}

/* Increase the volume */
void increase_volume(void)
{
	enum command command = AUDIO_VOLUME_UP;
        write(pipe_to_child, &command, sizeof(command));
}

/* Decrease the volume */
void decrease_volume(void)
{
        enum command command = AUDIO_VOLUME_DOWN;
        write(pipe_to_child, &command, sizeof(command));
}

/* Reset the volume to its default level */
void reset_volume(void)
{
        enum command command = AUDIO_VOLUME_RESET;
        write(pipe_to_child, &command, sizeof(command));
}
