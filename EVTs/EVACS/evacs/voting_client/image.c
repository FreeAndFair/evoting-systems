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
#include <assert.h>
#include <unistd.h>
#include <stdint.h>
#include <fcntl.h>
#include <errno.h>
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <png.h>
#include <common/http.h>
#include "image.h"
#include "voting_client.h"

#define USB_SERIAL_DEVICE "/dev/usb/ttyUSB0"

static int window_width;
static int window_height;

/* An image */
struct image {
	unsigned int width, height;
	XImage *image;
	struct image *highlighted_image;
};

/* Simple linked list of images (we don't have that many) */
struct image_list
{
	struct image_list *next;
	struct image image;
	/* Name hangs off end of structure */
	char name[0];
};

static struct image_list *image_cache = NULL;
static Display *x_display;
static Window x_window;
static bool upside_down;

/* Initialise the graphics display.
   This code taken from prototype prototypes/Graph-c-booth/Graph.c,
   Copyright (C) Andrew Tridgell 2001
 */
bool initialise_display(int scrn_width, int scrn_height, bool is_upside_down)
{
	Pixmap blank;
	XColor dummy;
	char data[1] = { 0 };
	Cursor cursor;
	XWMHints wmhint;
	XClassHint classhint;
	XEvent event;

	assert(!x_display);
	x_display = XOpenDisplay(NULL);
	if (!x_display)
		return false;

	window_width = scrn_width;
	window_height = scrn_height;

	/* Remember if we're upside down */
	upside_down = is_upside_down;

	/* window creation */
	/* SIPL 2011-11-15 The seventh parameter (border width) was 5.
	   It is now 0. */
	x_window = XCreateSimpleWindow(x_display, RootWindow(x_display, 0),
				       0, 0, window_width, window_height, 0, 
				       BlackPixel(x_display, 0), 
				       WhitePixel(x_display, 0));

	/* Tell Window Manager to give us Input Focus */
	wmhint.input = True;
	wmhint.flags = InputHint;
	XSetWMHints(x_display, x_window, &wmhint);
	classhint.res_name = NULL; classhint.res_class = NULL;
	XSetClassHint(x_display, x_window, &classhint);

	/* Set cursor to empty */
	blank = XCreateBitmapFromData(x_display, x_window, data, 1, 1);
	cursor = XCreatePixmapCursor(x_display, blank, blank, &dummy, &dummy, 0, 0);
	XFreePixmap(x_display, blank);
	XDefineCursor(x_display, x_window, cursor);

	/* We want all input events */
	XSelectInput(x_display, x_window, 0xFFFF);

	/* Map window, sync display, wait for it to show up */
	XMapRaised(x_display, x_window);
	XSync(x_display, 0);

	/* We should get an expose event */
	do {
		XNextEvent(x_display, &event);
	} while (event.type != Expose);

	/* Grab input focus */
	/*XSetInputFocus(x_display, x_window, RevertToNone, CurrentTime);*/

	/* Turn off keyboard repeat! */
	XAutoRepeatOff(x_display);

	/* Turn off screen blanking */
	XSetScreenSaver(x_display, 0, 0, 0, 0);

	return true;
}

/* DDS3.1.2: Paste Image */
void paste_image(unsigned x, unsigned y, struct image *image)
{
	unsigned int real_x, real_y;
	assert(x_display);

	/* If we're drawing upside down, we need to subtract the given
           coordinates from the bottom of the screen. */
	if (upside_down) {
		real_x = get_screen_width() - x - image->width;
		real_y = get_screen_height() - y - image->height;
	} else {
		real_x = x; 
		real_y = y;
	}

	XPutImage(x_display, x_window,
		  DefaultGC(x_display, DefaultScreen(x_display)), image->image,
		  0, 0, real_x, real_y, image->width, image->height);
	XSync(x_display, 0);
}

/* Clear the screen to all white */
bool clear_screen(void)
{
	XClearWindow(x_display, x_window);
	return true;
}

/* The colour of gray (in 5 bits) */
#define HIGHLIGHT_GRAY 20
static struct image *create_highlight(XImage *oldimage,
				      unsigned int width,
				      unsigned int height)
{
	unsigned int x, y;
	struct image *newimage;

	newimage = malloc(sizeof(*newimage));
	if (!newimage) return NULL;
	newimage->width = width;
	newimage->height = height;

	newimage->image = XCreateImage(x_display,
				       DefaultVisual(x_display,
						     DefaultScreen(x_display)),
				       oldimage->depth,
				       oldimage->format, 0, NULL,
				       width, height,
				       oldimage->bitmap_pad,
				       oldimage->bytes_per_line);
	if (!newimage->image) {
		free(newimage);
		return NULL;
	}
	newimage->image->data = malloc(newimage->image->bytes_per_line
				       * height);
	if (!newimage->image->data) {
		XDestroyImage(newimage->image);
		free(newimage);
		return NULL;
	}
	/* Copy data across */
	memcpy(newimage->image->data, oldimage->data,
	       newimage->image->bytes_per_line * height);
	
	for (x = 0; x < width; x++) {
		for (y = 0; y < height;y++) {
			uint16_t *ptr;

			ptr = (uint16_t *)newimage->image->data
				+ x + y*width;
			/* If any color brighter than grey, all grey */
			if (((*ptr >> 11) & 0x1f) > HIGHLIGHT_GRAY
			    || ((*ptr >> 6) & 0x1f) > HIGHLIGHT_GRAY
			    || (*ptr & 0x1f) > HIGHLIGHT_GRAY) {
				*ptr = (HIGHLIGHT_GRAY << 11)
					| (HIGHLIGHT_GRAY << 6)
					| (HIGHLIGHT_GRAY);
			}
		}
	}
	return newimage;
}

/* Function to "read" from the memory area */
static void my_read(png_structp png_ptr, png_bytep data, png_size_t length)
{
	void *ptr = png_get_io_ptr(png_ptr);

	memcpy(data, ptr, length);
	/* Reset read function with updated pointer */
	png_set_read_fn(png_ptr, ptr + length, my_read);
}

static XImage *png_to_ximage(void *buf, size_t size,
			     unsigned int *width, unsigned int *height)
{
	int bit_depth, color_type;
	png_structp png_ptr;
	png_infop info_ptr;
	unsigned int row;
	uint16_t *image_data;
	XImage *image;
	png_uint_32 w, h;
	int screen;

	png_ptr = png_create_read_struct(PNG_LIBPNG_VER_STRING,
					 (png_voidp)NULL, NULL, NULL);
	info_ptr = png_create_info_struct(png_ptr);

	png_set_read_fn(png_ptr, buf, my_read);
	png_read_info(png_ptr, info_ptr);
	png_get_IHDR(png_ptr, info_ptr, &w, &h, &bit_depth, &color_type,
		     NULL, NULL, NULL);
	if (color_type != PNG_COLOR_TYPE_RGB
	    && color_type != PNG_COLOR_TYPE_RGB_ALPHA) {
		fprintf(stderr, "PNG must be RGB or RGBA!\n");
		png_destroy_read_struct(&png_ptr, &info_ptr, NULL);
		return NULL;
	}
		
	if (bit_depth != 8) {
		fprintf(stderr, "PNG bit depth %i not 24!\n", bit_depth);
		png_destroy_read_struct(&png_ptr, &info_ptr, NULL);
		return NULL;
	}

	/* Discard any alpha channels */
	if (color_type & PNG_COLOR_MASK_ALPHA)
		png_set_strip_alpha(png_ptr);

	/* Create an X Image */
	screen = DefaultScreen(x_display);
	image = XCreateImage(x_display,
			     DefaultVisual(x_display, screen),
			     DefaultDepth(x_display, screen),
			     ZPixmap, 0, NULL,
			     w, h,
			     8, 0);
	if (!image) {
		png_destroy_read_struct(&png_ptr, &info_ptr, NULL);
		return NULL;
	}

	/* Now allocate space for it (16-bit == 2 bytes). */
	image_data = malloc(w * h * 2);
	if (!image_data) {
		XDestroyImage(image);
		png_destroy_read_struct(&png_ptr, &info_ptr, NULL);
		return NULL;
	}

	/* Do depth conversion on the fly as we read it. */
	for (row = 0; row < h; row++) {
		png_byte rowptr[w * 3];
		unsigned int x, real_x;
		unsigned int real_row;

		/* If they want it upside down, simply fill from the bottom */
		if (upside_down) real_row = h - row - 1;
		else real_row = row;

		png_read_row(png_ptr, rowptr, NULL);
		for (x = 0; x < w; x++) {
			unsigned int old_r, old_g, old_b;

			/* We want rotated, not mirror image! */
			if (upside_down) real_x = w - x - 1;
			else real_x = x;

			old_r = rowptr[x * 3];
			old_g = rowptr[x * 3 + 1];
			old_b = rowptr[x * 3 + 2];

			/* Five bits red, six green, five blue. */
			image_data[real_row * w + real_x] 
				= ((old_r >> 3) << 11)
				| ((old_g >> 2) << 5)
				| (old_b >> 3);
		}
	}
	png_destroy_read_struct(&png_ptr, &info_ptr, NULL);
	image->data = (void *)image_data;

	*width = w;
	*height = h;

	return image;
}

/* Given a URL, return the image or (or data = NULL for error). */
struct image *get_image(const char *url, bool with_highlight)
{
	char *buf;
	struct image_list *i;
	size_t size;

	/* If it's in the cache, return that */
	for (i = image_cache; i; i=i->next) 
		if (strcmp(i->name, url) == 0) return &i->image;

	/* Otherwise, create new cache entry. */
	i = malloc(sizeof(*i) + strlen(url)+1);
	if (!i) return NULL;
	strcpy(i->name, url);

	/* Ask server for image */
	buf = http_get(SERVER_ADDRESS, SERVER_PORT, url, &size);
	if (!buf) {
		free(i);
		return NULL;
	}

	i->image.image = png_to_ximage(buf, size,
				       &i->image.width, &i->image.height);
	if (!i->image.image) {
		free(buf);
		free(i);
		return NULL;
	}
	free(buf);

	if (with_highlight) {
		i->image.highlighted_image
			= create_highlight(i->image.image,
					   i->image.width, i->image.height);
		if (!i->image.highlighted_image) {
			free(i);
			return NULL;
		}
	} else {
		i->image.highlighted_image = NULL;
	}

	/* Sew it into head of list */
	i->next = image_cache;
	image_cache = i;
	return &i->image;
}

/* DDS3.2.11: Get Screen Width */
unsigned int get_screen_width(void)
{
	return window_width;
}

/* DDS????: Get Screen Height */
unsigned int get_screen_height(void)
{
	return window_height;
}

/* Draw error on the screen, fallback if images not available */
void draw_error(struct image *error, struct image *number, enum error err)
{
	if (error && number) {
		unsigned int ypos;

		ypos = (get_screen_height() - image_height(error))/2;
		/* Draw the error message in the middle */
		paste_image(0, ypos, error);
		ypos += image_height(error);
		/* And the error number centered below it */
		paste_image((get_screen_width() - image_width(number))/2,
			    ypos,
			    number);
	} else {
		/* Fallback code: screen of death, lines in binary */
#if 0
		unsigned int i;

		for (i = 0; i < 16; i++) {
			Imlib_Image img;

			img = imlib_create_image(window_width/16,
						 window_height);
			imlib_context_set_image(img);

			if ((unsigned int)err & (1 << i))
				imlib_context_set_color(0, 0, 0, 255);
			else
				imlib_context_set_color(255, 255, 255, 255);
			imlib_image_fill_rectangle(0, 0,
						   window_width/16,
						   window_height);
			imlib_render_image_on_drawable(i*window_width/16, 0);
			imlib_free_image();
		}
#endif
	}
}

/* Given an image, get the height or width */
unsigned int image_height(struct image *image)
{
	return image->height;
}

unsigned int image_width(struct image *image)
{
	return image->width;
}

/* DDS3.2.12: Highlight Image */
struct image *highlight_image(struct image *oldimage)
{
	assert(oldimage->highlighted_image);
	return oldimage->highlighted_image;
}

/* Close the display */
void close_display(void)
{
	/* Turn keyboard repeat back on! */
	XAutoRepeatOn(get_display());
	XDestroyWindow(x_display, x_window);
	XCloseDisplay(x_display);
	x_display=NULL;
}

/* For input.c to get the X display */
Display *get_display(void)
{
	return x_display;
}
