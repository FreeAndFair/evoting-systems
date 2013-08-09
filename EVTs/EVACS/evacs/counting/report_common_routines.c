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

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "report_common_routines.h"

#include <common/database.h>
#include <common/evacs.h>

#define LOG_FILE_NAME_STR_LEN 100

// ===================================================================
/*
   The routine get_date_and_time() is used to create a string
   specifying the current date and time in the format:

   <Day of Week> dd mmm yyyy hh:mm:ss

   where: hh is 00 .. 23.
*/
void get_date_and_time (      char   *time_str,
                        const size_t  str_len) {

  time_t     current_time;
  struct tm *ltime;

  time (&current_time);
  ltime = localtime(&current_time);

  strftime(time_str,
           str_len,
           "%A %d %B %Y  %X",
           ltime);
} // get_date_and_time()

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
FILE *open_log_file(const char *file_name,
                    const char *time_string) {

   extern FILE *stderr;
          FILE *err_file;
          char  name_of_file[LOG_FILE_NAME_STR_LEN];

   strcpy(name_of_file, LOG_FILE_DIR);
   strcat(name_of_file, file_name);
   strcat(name_of_file, "_");
   strcat(name_of_file, get_operator_id());
   strcat(name_of_file, ".txt");

   err_file = freopen(name_of_file, "w", stderr);
   fprintf(stderr, "Log file: %s created on %s\n\n",
           name_of_file,
           time_string);
   return err_file;

} // open_log_file()


// -------------------------------------------------------------------
/*
  The routine close_log_file() closes the currently open debugging
   log file.
  Information being written to the standard error device, which was
   being redirected to the debugging log file, is redirected to the
   standard output device; i.e. the terminal.
*/
void close_log_file(void) {

   char  time_string[TIME_STR_LEN];

   get_date_and_time(time_string, TIME_STR_LEN);
   fprintf(stderr, "\nLog file closed at %s\n", time_string);
   fflush(stderr);
   freopen("/dev/tty1", "w", stderr);

} // close_log_file()

// ===========================================================================
/*
  The routine 'page_start_postscript' is used to insert comments into the
   postscript code indicating the start of a new page.
*/
 void page_start_postscript(      FILE *out,
                            const int   page_number) {

   fprintf(stderr, "\nEntered page_start_postscript\n");
   fprintf(stderr, "   page_number: %d\n", page_number);

   fputs("%%Page: ", out);
   fprintf(out, "%d %d\n", page_number, page_number);

   fprintf(stderr, "Leaving page_start_postscript\n");
} // page_start_postscript()

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
void a4_page_end_postscript(      FILE *out,
                            const int   page_number,
                            const int   last_page) {

   fprintf(stderr, "\nEntered a4_page_end_postscript\n");
   fprintf(stderr, "   page_number: %d\n", page_number);

   fputs("showpage\n", out);
   fputs("%%PageTrailer\n", out);

   if (last_page) {
      fprintf(stderr, "This is the past page.\n");

      fputs("%%Trailer\n", out);
      fputs("%%BoundingBox: 0 0 ", out);
      fprintf(out, "%u %u\n", A4_PAGE_WIDTH, A4_PAGE_HEIGHT);
      fputs("%%Pages: ", out);
      fprintf(out, "%d\n", page_number);
      fputs("%%EOF\n", out);
   }
   fprintf(stderr, "Leaving a4_page_end_postscript\n");
} // a4_page_end_postscript()

// ---------------------------------------------------------------------------
/*
  The routine 'create_postscript_a4_page' is used to create a postscript
   file for an A4 page.
*/
FILE *create_postscript_a4_page(const char *name,
                                const char *time_string,
                                const char *table_title) {

   FILE  *ps_file;

   fprintf(stderr, "\nEntered create_postscript\n");
   fprintf(stderr, "   name: .......... '%s'\n", name);
   fprintf(stderr, "   time_string: ... '%s'\n", time_string);
   fprintf(stderr, "   table_title: ... '%s'\n", table_title);

   ps_file = fopen(name, "w");
   if (!ps_file) {
      fprintf(stderr,
              "Could not open %s for writing: %s - Terminating Program\n",
              name,
              strerror(errno));

      close_log_file();
      bailout("Could not open %s for writing: %s\n",
              name,
              strerror(errno));
   }

   fputs("%!PS-Adobe-1.0\n", ps_file);
   fputs("%%DocumentFonts: Helvetica Helvetica-Bold\n", ps_file);
   fputs("%%Title: ", ps_file);
   fprintf(ps_file, "%s\n", table_title);
   fputs("%%Creator: eVACS Report\n", ps_file);
   fputs("%%CreationDate: ", ps_file);
   fprintf(ps_file, "%s\n", time_string);
   fputs("%%BoundingBox: 0 0 ", ps_file);
   fprintf(ps_file, "%u %u\n", A4_PAGE_WIDTH, A4_PAGE_HEIGHT);

   fputs("%%DocumentMedia: Regular ", ps_file);
   fprintf(ps_file, "%u %u 0 () ()\n", A4_PAGE_WIDTH, A4_PAGE_HEIGHT);
   fputs("%%DocumentPaperSizes: A4\n", ps_file);
   fputs("%%PaperSize: A4\n", ps_file);

   fputs("%%Orientation: Portrait\n", ps_file);
   fputs("%%Pages: (atend)\n", ps_file);
   fputs("%%EndComments\n", ps_file);
   fputs("%%EndProlog\n", ps_file);

   fprintf(stderr, "Leaving create_postscript_a4_page\n");
   return ps_file;

} // create_postscript_a4_page()


// ---------------------------------------------------------------------------
/*
  The routine 'close_postscript' is used to close the postscript file.
*/
void close_postscript(FILE *out) {
   fclose(out);
} // close_postscript()

// ===========================================================================
/*
  The routine 'max_length' writes postscript code to canculate the length of
   the text (input parameter title) in the current font and fontsize.
  The calculated value is left on the postscript stack.
*/
void max_length(      FILE *out,
                const char *title) {

  fprintf(out, "(%s) stringwidth pop\n", title);

  /* Add a little padding */
  fprintf(out, "%u add\n", SMIDGE * 2);

} // max_length()

// ---------------------------------------------------------------------------
/*
  The routine 'draw_box' is used to draw a box, and to place text inside
   the box.
  The current position on the page is used as the top left hand side of the
   box.
  The width of the box is to be found on the postscript stack.
  The routine's parameters are:
  - out      - the postscript file to which the drawing and writing is to occur.
  - height   - the height of the box.
  - label    - the text to be written in the box.
  - fontsize - the size of the text.
  - orient   - whether the text is to be written vertically or horizontally.
  - justify  - the justification of the text inside the box (i.e. left, centred, or
                right justified).
  - grey_box - indicates whether the box is to be coloured grey.
*/
static void draw_box(      FILE                *out,
                     const unsigned int         height,
                     const char               *label,
                     const unsigned int        fontsize,
                     const enum orientation    orient,
                     const enum justification  justify,
                     const unsigned int        grey_box) {

   // fprintf(stderr, "\nEntered draw_box\n");

   // Need four copies of the width
   fprintf(out, "dup dup dup\n");

   /* Draw box: this uses two copies. */
   fprintf(out, "gsave 0 rlineto 0 -%u rlineto ", height);
   fprintf(out, "neg 0 rlineto 0 %u rlineto ", height);

   if (grey_box) {
      fprintf(out, "gsave\n");
      fprintf(out, "0.75 setgray\n");
      fprintf(out, "fill\n");
      fprintf(out, "stroke grestore\n");
   }

   fprintf(out, "stroke grestore\n");
   fprintf(out, "gsave ");

   /* Specify where the text is to start */

   if (justify == JUSTIFY_LEFT) {
       fprintf(out, "pop 0 -%u rmoveto ", height/2);
   } else if (justify == JUSTIFY_CENTRE) {
      fprintf(out, "2 div -%u rmoveto ", height/2);
   } else {
      fprintf(out, "-%u rmoveto ", height/2);
     }


   /* If vertical, rotate, and move across a little. */

   if (orient == ORIENT_VERTICAL)
      fprintf(out, "-%u 0 rmoveto -90 rotate ", fontsize/3);
   else
      fprintf(out, "0 -%u rmoveto ", fontsize/3);

   /* Figure label height and width, move back half of it. */
   if (grey_box)
      fprintf(out, "/Helvetica-bold findfont ");
   else
      fprintf(out, "/Helvetica findfont ");

   fprintf(out, "%u scalefont setfont ", fontsize);

   if (justify == JUSTIFY_LEFT) {
      fprintf(out, "(%s)", label);

   } else if (justify == JUSTIFY_CENTRE) {
        fprintf(out,
                "(%s) dup stringwidth "
                   " 2 div neg 2 1 roll 2 div neg 2 1 roll rmoveto ",
                label);
   } else {
        max_length (out, label);
        fprintf(out, "neg 0 rmoveto (%s)", label);
     }

   /* Draw it */
   fprintf(out, " show\n");

   fprintf(out, "grestore ");

   /* Move to the right: this uses the final copy. */
   fprintf(out, "0 rmoveto\n");

   // fprintf(stderr, "Leaving draw_box\n");
} // draw_box()

// ---------------------------------------------------------------------------
/*
  The routine '__write_text_in_box' is used to write text onto a page in an area
   bounded by a box (which is not drawn) of a specified size.
  The current position on the page is used as the top left hand corner of
   the box.
  The width of the box is to be found on the postscript stack.
  The routine's input parameters are:
  - out      - the postscript file to which the drawing and writing is to occur.
  - height   - the height of the box.
  - fontsize - the size of the text.
  - text     - the text to be written in the box.
  - orient   - whether the text is to be written vertically or horizontally.
  - justify  - the justification of the text inside the box (i.e. left, centred, or
                right justified).
  - box_text - indicates whether the text is to be bolded.
*/
static void __write_text_in_box (      FILE               *out,
                                 const unsigned int        height,
                                 const unsigned int        fontsize,
                                 const char               *text,
                                 const enum orientation    orient,
                                 const enum justification  justify,
                                 const unsigned int        bold_text) {

   // fprintf(stderr, "\nEntered __write_text_in_box\n");
   // fprintf(stderr, "   height: . %u\n", height);
   // fprintf(stderr, "   fontsize: %u\n", fontsize);
   // fprintf(stderr, "   text: ... '%s'\n", text);

   /* Specify where the text is to start */

   fprintf(out, "gsave\n");
   if (justify == JUSTIFY_LEFT) {
       fprintf(out, "pop 0 -%u rmoveto ", height/2);
   } else if (justify == JUSTIFY_CENTRE) {
      fprintf(out, "2 div -%u rmoveto ", height/2);
   } else {
      fprintf(out, "-%u rmoveto ", height/2);
     }


   /* If vertical, rotate, and move across a little. */

   if (orient == ORIENT_VERTICAL)
      fprintf(out, "-%u 0 rmoveto -90 rotate ", fontsize/3);
   else
      fprintf(out, "0 -%u rmoveto ", fontsize/3);

   /* Figure label height and width, move back half of it. */

   if (bold_text) {
      fprintf(out, "/Helvetica-bold findfont ");
   } else {
        fprintf(out, "/Helvetica findfont ");
     }

   fprintf(out, "%u scalefont setfont \n", fontsize);

   if (justify == JUSTIFY_LEFT) {
      fprintf(out, "3 0 rmoveto (%s)", text);

   } else if (justify == JUSTIFY_CENTRE) {
        fprintf(out,
                "(%s) dup stringwidth "
                   " 2 div neg 2 1 roll 2 div neg 2 1 roll rmoveto ",
                text);
   } else {
        max_length (out, text);
        fprintf(out, "neg 0 rmoveto (%s)", text);
     }
   fprintf(out, " show grestore\n");
} // __write_text_in_box()

// ---------------------------------------------------------------------------
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
unsigned int draw_text_box(      FILE               *out,
                           const unsigned int        width,
                           const unsigned int        height,
                           const char               *label,
                           const unsigned int        fontsize,
                           const enum orientation    orient,
                           const enum justification  justify,
                           const unsigned int        grey_box) {

   // fprintf(stderr, "\nEntered draw_text_box\n");
   // fprintf(stderr, "   width: .. %u\n", width);
   // fprintf(stderr, "   height: . %u\n", height);
   // fprintf(stderr, "   label: .. '%s'\n", label);
   // fprintf(stderr, "   fontsize: %u\n", fontsize);

   fprintf(out, "%u\n", width);

   draw_box(out, height, label, fontsize, orient, justify, grey_box);

   // fprintf(stderr, "Leaving draw_text_box: returning width of %u\n", width);
   return width;

} // draw_text_box()


// ---------------------------------------------------------------------------
/*
  The routine '__draw_empty_box' is used to draw a box of a specified
   size.
  Text is not written into the box.
  The width of the box is to be found on the postscript stack.
  The routine's parameters are:
  - out      - the postscript file to which the drawing and writing is to occur.
  - height   - the height of the box.
  - grey_box - indicates whether the box is to be coloured grey.
*/
static void __draw_empty_box(      FILE         *out,
                             const unsigned int  height,
                             const unsigned int  grey_box) {

   // fprintf(stderr, "\nEntered __draw_empty_box\n");

   /* Need two copies of width */
   fprintf(out, "dup dup\n");

   /* Draw box: this uses two copies. */
   fprintf(out, "gsave 0 rlineto 0 -%u rlineto ", height);
   fprintf(out, "neg 0 rlineto 0 %u rlineto ", height);

   if (grey_box) {
      fprintf(out, "gsave\n");
      fprintf(out, "0.75 setgray\n");
      fprintf(out, "fill\n");
      fprintf(out, "stroke grestore\n");
   }

   fprintf(out, "stroke grestore\n");

   /* Move to the right: this uses the final copy. */
   fprintf(out, "0 rmoveto\n");

   // fprintf(stderr, "Leaving __draw_empty_box\n");
} // __draw_empty_box()


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
unsigned int draw_empty_box(      FILE               *out,
                            const unsigned int        width,
                            const unsigned int        height,
                            const unsigned int        grey_box) {

   // fprintf(stderr, "\nEntered draw_empty_box\n");
   // fprintf(stderr, "   width: .. %u\n", width);
   // fprintf(stderr, "   height: . %u\n", height);

   fprintf(out, "%u\n", width);

   __draw_empty_box(out, height, grey_box);

   // fprintf(stderr, "Leaving draw_empty_box: returning width of %u\n", width);
   return width;

} // draw_empty_box()

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
void write_text(      FILE               *out,
                const unsigned int        width,
                const unsigned int        height,
                const unsigned int        fontsize,
                const char               *text,
                const enum orientation    orient,
                const enum justification  justify,
                const unsigned int        bold_text) {

   // fprintf(stderr, "\nEntered write_text\n");
   // fprintf(stderr, "   width: ... %u\n", width);
   // fprintf(stderr, "   height: .. %u\n", height);
   // fprintf(stderr, "   fontsize:  %u\n", fontsize);
   // fprintf(stderr, "   text: .... '%s'\n", text);
   // fprintf(stderr, "   bold_text: %u\n", bold_text);

   fprintf(out, "%u\n", width);

   __write_text_in_box(out, height, fontsize, text, orient, justify, bold_text);

} // write_text()

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
                       const unsigned int  to_y) {

   fprintf(out, "gsave\n");
   fprintf(out, "%u %u moveto\n", from_x, from_y);
   fprintf(out, "%u %u lineto\n", to_x, to_y);
   fprintf(out, "stroke grestore\n");
} // draw_line();
