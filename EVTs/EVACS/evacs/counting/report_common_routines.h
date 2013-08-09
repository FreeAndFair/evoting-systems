#ifndef _RPT_COMN_H
#define _RPT_COMN_H

/* This file is (C) copyright 2007 Software Improvements, Pty Ltd */

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
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  */

#define POINTS_IN_MM     2.834645669
#define SMIDGE           2

#define TIME_STR_LEN     50
#define A4_PAGE_WIDTH    595
#define A4_PAGE_HEIGHT   842
#define MIDDLE_A4_PAGE_X A4_PAGE_WIDTH / 2

#define LOG_FILE_DIR "/tmp/"

/* The enum 'justification' is used to indicate whether text is to be
    left, centre, or right justified horizontally within a spcified
    box.
*/
enum justification {JUSTIFY_LEFT, JUSTIFY_CENTRE, JUSTIFY_RIGHT};

/* The enum 'orientation' is used to indicate whether text is to be
    written horizontally or vertically within a specified box.
   Only horizontal orientation is being used currently; the
    vertical orientation has not been tested.
*/
enum orientation {ORIENT_HORIZONTAL, ORIENT_VERTICAL};


// ===================================================================
/*
   The routine get_date_and_time() is used to create a string
   specifying the current date and time in the format:

   <Day of Week> dd mmm yyyy hh:mm:ss

   where: hh is 00 .. 23.
*/
extern void get_date_and_time (      char   *time_str,
                               const size_t  str_len);

// -------------------------------------------------------------------
/*
   The routine open_log_file() is used to create a disk file to which
    debugging information is written.
   The routine redirect information being written to the standard
    error device to the log file.
   The routine writes the name of the file and the file's creation
    date and time to the file.
   Note: Only one debugging log file can be open at a time by a program.
*/
extern FILE *open_log_file(const char *file_name,
                           const char *time_string);

// -------------------------------------------------------------------

/*
  The routine close_log_file() closes the currently open debugging
   log file.
  Information being written to the standard error device, which was
   being redirected to the debugging log file, is redirected to the
   standard output device; i.e. the terminal.
*/
extern void close_log_file(void);

// ===========================================================================

/*
  The routine 'page_start_postscript' is used to insert comments into the
   postscript code indicating the start of a new page.
*/
extern void page_start_postscript(      FILE *out,
                                  const int   page_number);

// ---------------------------------------------------------------------------
/*
  The routing 'a4_page_end_postscript' is used to add comments into the
   postscript code to indicate the end of a page.
  The comments includes specifying 'BoundingBox' - indicating an A4
   page.
  If the input parameter 'last_page' is not '0', then comments will be
   added indicatine the end of the postscript file, including the total
   number of pages.
*/
extern void a4_page_end_postscript(      FILE *out,
                                   const int   page_number,
                                   const int   last_page);

// ---------------------------------------------------------------------------
/*
  The routine 'create_postscript_a4_page' is used to create a postscript
   file for an A4 page.
*/
extern FILE *create_postscript_a4_page(const char *name,
                                       const char *time_string,
                                       const char *title_string);


// ---------------------------------------------------------------------------
/*
  The routine 'close_postscript' is used to close the postscript file.
*/
extern void close_postscript(FILE *out);


// ===========================================================================
/*
  The routine 'max_length' writes postscript code to canculate the length of
   the text (input parameter title) in the current font and fontsize.
  The calculated value is left on the postscript stack.
*/
extern void max_length(      FILE *out,
                       const char *title);

// ===========================================================================
/*
  The routine 'draw_text_box' is used to draw a box, and to place text inside
   the box.
  The current position on the page is used as the top left hand side of the
   box.
  The routine's parameters are:
  - out      - the postscript file to which the drawing and writing is to occur.
  - width    - the width of the box.
  - height   - the height of the box.
  - label    - the text to be written in the box.
  - fontsize - the size of the text.
  - orient   - whether the text is to be written vertically or horizontally.
  - justify  - the justification of the text inside the box (i.e. left, centred, or
                right justified).
  - grey_box - indicates whether the box is to be coloured grey.
*/
extern unsigned int draw_text_box(      FILE               *out,
                                  const unsigned int        width,
                                  const unsigned int        height,
                                  const char               *label,
                                  const unsigned int        fontsize,
                                  const enum orientation    orient,
                                  const enum justification  justify,
                                  const unsigned int        grey_box);

// ---------------------------------------------------------------------------
/*
  The routine 'draw_empty_box' is used to draw a box of a specified
   size.
  Text is not written into the box.
  The routine's parameters are:
  - out      - the postscript file to which the drawing and writing is to occur.
  - width    - the width of the box.
  - height   - the height of the box.
  - grey_box - indicates whether the box is to be coloured grey.
*/
extern unsigned int draw_empty_box(      FILE         *out,
                                   const unsigned int  width,
                                   const unsigned int  height,
                                   const unsigned int  grey_box);


// ---------------------------------------------------------------------------
/*
  The routine 'write_text' is used to write text onto a page in an area
   bounded by a box (which is not drawn) of a specified size.
  The current position on the page is used as the top left hand corner of
   the box.
  The routine's input parameters are:
  - out      - the postscript file to which the drawing and writing is to occur.
  - width    - the width of the box.
  - height   - the height of the box.
  - fontsize - the size of the text.
  - text     - the text to be written in the box.
  - orient   - whether the text is to be written vertically or horizontally.
  - justify  - the justification of the text inside the box (i.e. left, centred, or
                right justified).
  - box_text - indicates whether the text is to be bolded.
*/
extern void write_text (      FILE               *out,
                        const unsigned int        width,
                        const unsigned int        height,
                        const unsigned int        fontsize,
                        const char               *text,
                        const enum orientation    orient,
                        const enum justification  justify,
                        const unsigned int        bold_text);


// ---------------------------------------------------------------------------
/*
  The routine 'draw_line' is used to draw a line between two absolute points
   on the page.
  The routine's input parameters are:
  - out            - the postscript file to which the drawing and writing is
                      to occur.
  - from_x, from_y - the starting point of the line being drawn.
  - to_x,   to_y   - the end point of the line being drawn.
*/
extern void draw_line (      FILE         *out,
                       const unsigned int  from_x,
                       const unsigned int  from_y,
                       const unsigned int  to_x,
                       const unsigned int  to_y);

#endif /*_REPORT_COMMON_H*/
