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
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <stdlib.h>
#include <assert.h>
#include <common/evacs.h>
#include "report.h"

#define TITLE_FONT_SIZE 18
#define CANDIDATE_FONT_SIZE 12
#define NORMAL_COLUMN_WIDTH 40
#define FRACTION_COLUMN_WIDTH (NORMAL_COLUMN_WIDTH*3)
#define CANDIDATE_COLUMN_HEIGHT 160
#define NORMAL_COLUMN_HEIGHT 40
#define GROUP_HEIGHT 15
#define TOP_BOX_HEIGHT (GROUP_HEIGHT + CANDIDATE_COLUMN_HEIGHT)
#define GROUP_FONT_SIZE 8
#define COLUMN_TITLE_FONT_SIZE 10
#define TOP_LEFT_INFO_FONT_SIZE 8
#define NORMAL_FONT_SIZE 10
#define NUMBER_FONT_SIZE 14
#define DESCRIP_FONT_SIZE 18
#define COUNT_NUMBER_FONT "Helvetica-Bold"
#define SMIDGE 2

/* simple counter incremented each time someone is elected */
static unsigned int order_elected = 0;

/* Keep track of previous majority in order to report twice on same count ONLY when changed*/
static unsigned int previous_count = 0;
static unsigned int previous_majority=0;

enum orientation {
	ORIENT_HORIZONTAL,
	ORIENT_VERTICAL,
};

#define TOP 0
#define BOTTOM 1
struct
{
	FILE *out;
	FILE *raw;
	/* Where are the columns? */
	unsigned int exhausted, counted, transfer_value, to_table2;
	/* How many formal votes are there? */
	unsigned int num_formals;
	/* How many informal votes are there? */
	unsigned int num_informals;
	/* The electorate name */
	char *ename;
	/* The descriptions for each count */
	char *count_descrip[2][MAX_COUNTS];
} counting;

struct
{
	FILE *out;
	FILE *raw;
	/* Where are the columns? */
	unsigned int exhausted, loss_gain, total, remark;
	/* How many formal papers did we have */
	unsigned int num_formals;
	/* How many seats are there? */
	unsigned int num_seats;
	/* What's the quota? (0 if not set) */
	unsigned int quota;
	/* What's the vacancy total votes (0 if not set) */
	unsigned int vacancy_total_votes;
	/* What's the vacancy total ballots (0 if not set) */
	unsigned int vacancy_total_ballots;
	/* The electorate name */
	char *ename;
	/* The total exhausted votes up to now */
	unsigned int total_exhausted;
	/* The running total of losses */
	int total_loss;
	/* The remarks for each count */
	char *remarks[2][MAX_COUNTS];
} distribution;

void reset_order_elected(void) {
        order_elected = 0;
}

unsigned int increment_order_elected(void) {
	return ++order_elected; 
}

unsigned int  get_order_elected(void) {
	return order_elected; 
}
static FILE *create_postscript(const char *name)
{
	FILE *ret;
	time_t now;

	ret = fopen(name, "w");
	if (!ret) bailout("Could not open %s for writing: %s\n",
			  name, strerror(errno));
	fputs("%!PS-Adobe-1.0\n", ret);
	fputs("%%DocumentFonts: Helvetica Helvetica-Bold\n", ret);
	fputs("%%Title: Scrutiny Sheet\n", ret);
	fputs("%%Creator: counting (GPL)\n", ret);
	fputs("%%CreationDate: ", ret);
	time(&now);
	fprintf(ret, "%s\n", ctime(&now));
	fputs("%%EndComments\n", ret);
	fputs("%%EndProlog\n", ret);
	fputs("%%Page: 0 1\n", ret);
	/* If image goes -ve, then bounding box calculation fails;
		allow for 6+ A3 pages of count lines (A3 landscape w/margins = 791points printable) */
	fputs("2000 5500 translate\n", ret);

	return ret;
}

/* Draw box, given width is already on stack */
static void __draw_box(FILE *out,
		       unsigned int height,
		       const char *label,
		       unsigned int fontsize,
		       enum orientation orient,
		       bool centre)
{
	/* Need four copies of width */
	fprintf(out, "dup dup dup\n");

	/* Draw box: this uses two copies. */
	fprintf(out, "gsave 0 rlineto 0 -%u rlineto ", height);
	fprintf(out, "neg 0 rlineto 0 %u rlineto ", height);
	fprintf(out, "stroke grestore\n");

	fprintf(out, "gsave ");
	/* Move to the middle: this uses one copy */
	fprintf(out, "2 div -%u rmoveto ", height/2);

	/* If vertical, rotate, and move across a little. */
	if (orient == ORIENT_VERTICAL)
		fprintf(out, "-%u 0 rmoveto -90 rotate ", fontsize/3);
	else
		fprintf(out, "0 -%u rmoveto ", fontsize/3);

	/* Figure label height and width, move back half of it. */
	fprintf(out, "/Helvetica findfont ");
	fprintf(out, "%u scalefont setfont ", fontsize);
	if (centre) {
	        fprintf(out, "(%s) dup stringwidth "
			" 2 div neg 2 1 roll 2 div neg 2 1 roll rmoveto ", label);
	} else {
	        fprintf(out, "(%s) dup stringwidth "
			" 2 div neg 2 1 roll 2 div neg 2 1 roll rmoveto ", label);
	}
	/* Draw it */
	fprintf(out, "show\n");

	fprintf(out, "grestore ");

	/* Move to the right: this uses the final copy. */
	fprintf(out, "0 rmoveto\n");
}

/* Draw box with top left at the current location, and move cursor across */
static unsigned int draw_box(FILE *out,
			     unsigned int width, unsigned int height,
			     const char *label, unsigned int fontsize,
			     enum orientation orient,
			     bool centre)
{
	fprintf(out, "%u\n", width);
	__draw_box(out, height, label, fontsize, orient, centre);
	return width;
}

static unsigned int draw_candidate_headings(FILE *out,
					    struct cand_list *candidates)
{
	unsigned int ret;
	unsigned int num_in_group;
	struct group *group;
	struct cand_list *i;
	unsigned int count = 0;
	FILE *raw_stream;
	
	if (out == counting.out) 
		raw_stream = counting.raw;
	else
		raw_stream = distribution.raw;

	fputs("0 0 moveto\n", out);

	/* Draw group headings */
	for (i = candidates; i; ) {
		/* Candidates must be in order */
		group = i->cand->group;
		num_in_group = 0;
		do {
		/* output raw data */
		fprintf(raw_stream,"CN:%u:%s:%s\n",count,group->abbrev,i->cand->name);
		  assert(i->cand->scrutiny_pos == count);
			count++;
			num_in_group++;
			i = i->next;
		} while (i && i->cand->group == group);

		/* Draw group box with name in it. */
		draw_box(out,
			 num_in_group * NORMAL_COLUMN_WIDTH,
			 GROUP_HEIGHT,
			 group->abbrev,
			 GROUP_FONT_SIZE,
			 ORIENT_HORIZONTAL, true);
	}

	/* Draw candidates */
	fprintf(out, "0 -%u moveto\n", GROUP_HEIGHT);
	for (i = candidates, ret = 0; i; i = i->next) {
		ret += draw_box(out,
				NORMAL_COLUMN_WIDTH,
				CANDIDATE_COLUMN_HEIGHT,
				i->cand->name,
				CANDIDATE_FONT_SIZE,
				ORIENT_VERTICAL, false);
		/* output raw data  */
		
	}

	/* Move up to top height. */
	fprintf(out, "0 %u rmoveto\n", GROUP_HEIGHT);
	return ret;
}

static void draw_counting_columns(struct cand_list *candidates)
{
	counting.exhausted = draw_candidate_headings(counting.out, candidates);
	counting.counted
		= counting.exhausted 
		+ draw_box(counting.out,
			   NORMAL_COLUMN_WIDTH,
			   TOP_BOX_HEIGHT,
			   "Papers Exhausted at Count",
			   COLUMN_TITLE_FONT_SIZE,
			   ORIENT_VERTICAL,true);
	counting.transfer_value
		= counting.counted
		+ draw_box(counting.out,
			   NORMAL_COLUMN_WIDTH,
			   TOP_BOX_HEIGHT,
			   "Total Papers Counted",
			   COLUMN_TITLE_FONT_SIZE,
			   ORIENT_VERTICAL, true);
	counting.to_table2
		= counting.transfer_value
		+ draw_box(counting.out,
			   FRACTION_COLUMN_WIDTH,
			   TOP_BOX_HEIGHT,
			   "Transfer Value",
			   COLUMN_TITLE_FONT_SIZE,
			   ORIENT_VERTICAL, true);

	draw_box(counting.out,
		 NORMAL_COLUMN_WIDTH,
		 TOP_BOX_HEIGHT,
		 "Votes transferred to Table II",
		 COLUMN_TITLE_FONT_SIZE,
		 ORIENT_VERTICAL, true);
}

static void draw_distribution_columns(struct cand_list *candidates)
{
	distribution.exhausted = draw_candidate_headings(distribution.out,
							 candidates);
	distribution.loss_gain
		= distribution.exhausted
		+ draw_box(distribution.out,
			   NORMAL_COLUMN_WIDTH,
			   TOP_BOX_HEIGHT,
			   "Votes Exhausted at Count",
			   COLUMN_TITLE_FONT_SIZE,
			   ORIENT_VERTICAL, true);
	distribution.total
		= distribution.loss_gain
		+ draw_box(distribution.out,
			   NORMAL_COLUMN_WIDTH,
			   TOP_BOX_HEIGHT,
			   "Loss by fraction",
			   COLUMN_TITLE_FONT_SIZE,
			   ORIENT_VERTICAL, true);
	distribution.remark
		= distribution.total
		+ draw_box(distribution.out,
			   NORMAL_COLUMN_WIDTH,
			   TOP_BOX_HEIGHT,
			   "Total votes at End of the Count",
			   COLUMN_TITLE_FONT_SIZE,
			   ORIENT_VERTICAL, true);
}

void report_start(const struct election *e, const struct candidate *vacating)
{
	unsigned int i;
	char * table1_name;
	char * table2_name;

	memset(&counting, 0, sizeof(counting));
	memset(&distribution, 0, sizeof(distribution));

	counting.ename = strdup(e->electorate->name);
	counting.out = create_postscript("/tmp/table1.ps");
	fflush(counting.out);
	table1_name = malloc(sizeof(char) * (strlen("/tmp/table1.dat") + strlen(counting.ename) + 2));
	sprintf(table1_name, "%s%s%s", "/tmp/table1.", counting.ename, ".dat");
	counting.raw = fopen(table1_name, "w");
	free(table1_name);
	if (!counting.raw) 
		bailout("Could not open /tmp/table1.dat for writing: %s\n",
			strerror(errno));

	distribution.ename = strdup(e->electorate->name);
	distribution.total_exhausted = 0;
	distribution.total_loss = 0;
	distribution.out = create_postscript("/tmp/table2.ps");
	table2_name = malloc(sizeof(char) * (strlen("/tmp/table2.dat") + strlen(distribution.ename) + 2));
	sprintf(table2_name, "%s%s%s", "/tmp/table2.", distribution.ename, ".dat");
        distribution.raw = fopen(table2_name, "w");
	free(table2_name);
	if (!distribution.raw) 
		bailout("Could not open /tmp/table2.dat for writing: %s\n",
			strerror(errno));

	/* Start with empty remarks and counts */
	for (i = 0; i < MAX_COUNTS; i++) {
		distribution.remarks[TOP][i] = NULL;
		distribution.remarks[BOTTOM][i] = NULL;
		counting.count_descrip[TOP][i] = NULL;
		counting.count_descrip[BOTTOM][i] = NULL;
	}
	/* Fixed remarks for first count */
	if (! vacating)
		counting.count_descrip[BOTTOM][0] 
			= strdup("First choice of all papers");
	draw_counting_columns(e->candidates);
	draw_distribution_columns(e->candidates);
}

/* externally visible routine to append a new line to counting raw data*/
void counting_raw_newline() {
	fprintf(counting.raw,"\n");
}

/* Get the quota (for casual vacancy) */
unsigned int report_get_quota(void)
{
	return distribution.quota;
}

/* Leave the length of the longest string on the stack */
static void max_length(FILE *out,
		       const char *title,
		       char *top_strings[],
		       char *bottom_strings[],
		       unsigned int num_strings)
{
	unsigned int i;

	fprintf(out, "(%s) stringwidth pop\n", title);
	for (i = 0; i < num_strings; i++) {
		fprintf(out, "(%s) stringwidth pop\n", top_strings[i]);
		fprintf(out, "(%s) stringwidth pop\n", bottom_strings[i]);
	}

	/* If stack - 2 < stack - 1, swap them.  Then pop top of stack */
	for (i = 0; i < num_strings*2; i++)
		fprintf(out, "2 copy lt { 2 1 roll } if pop\n");

	/* Add a little padding */
	fprintf(out, "%u add\n", SMIDGE*2);
}

/* Draw an "H" with the upper string in the top of the H, and the
   lower string in the bottom, at the current location, and move down.
   Width is taken from the stack. */
static void draw_pair(FILE *out, const char *upper, const char *lower,
		      unsigned int fontsize, bool centre)
{
	/* Draw "H", starting at top left. */
	fprintf(out, "gsave 0 -%u rlineto 0 %u rmoveto"
		" dup 0 rlineto 0 %u rmoveto 0 -%u rlineto stroke grestore\n",
		NORMAL_COLUMN_HEIGHT, NORMAL_COLUMN_HEIGHT/2,
		NORMAL_COLUMN_HEIGHT/2, NORMAL_COLUMN_HEIGHT);

	/* NULL strings become empty strings */
	if (!upper) upper = "";
	if (!lower) lower = "";

	fprintf(out, "gsave\n");
	if (centre) {
		/* Move to centre of crossbar: removes width from stack. */
		fprintf(out, "2 div -%u rmoveto\n",
			NORMAL_COLUMN_HEIGHT/2);
		
		
		fprintf(out, "gsave (%s) dup stringwidth\n", upper);
					
		/* Now have width (and height) on stack.  Move by
                   -W/2, +SMIDGE. */
		fprintf(out, "pop 2 div neg %u rmoveto\n", SMIDGE);
		/* Draw string */
		fprintf(out, "show grestore\n");
		
		fprintf(out, "gsave (%s) dup stringwidth\n", lower);
		
		/* Now have width (and height) on stack.  Move by
		   -W/2, -H-SMIDGE. */
		fprintf(out, "pop 2 div neg -%u rmoveto\n",
			fontsize+SMIDGE);
		/* Draw string */
		fprintf(out, "show grestore\n");
	} else {
		/* Remove width from stack */
		fprintf(out, "pop\n");
		/* Move to top left edge of crossbar */
		fprintf(out, "gsave 0 -%u rmoveto\n",
			NORMAL_COLUMN_HEIGHT/2-SMIDGE);
		/* Draw string */
		fprintf(out, "(%s) show grestore\n", upper);
				
		/* Move to bottom left edge of crossbar */
		fprintf(out, "gsave 0 -%u rmoveto\n",
			NORMAL_COLUMN_HEIGHT/2+fontsize);
		/* Draw string */
		fprintf(out, "(%s) show grestore\n", lower);
		
	}

	/* Move down */
	fprintf(out, "grestore 0 -%u rmoveto\n", NORMAL_COLUMN_HEIGHT);
}

/* Draw a number pair at the given location */
static void draw_number_pair(FILE *out,
			     unsigned int xpos,
			     unsigned int line,
			     int upper,
			     int lower)
{
	char upperstr[INT_CHARS+1], lowerstr[INT_CHARS+1];

	/* Set font */
	fprintf(out, "/Helvetica findfont ");
	fprintf(out, "%u scalefont setfont ", NORMAL_FONT_SIZE);

	sprintf(upperstr, "%i", upper);
	sprintf(lowerstr, "%i", lower);
	/* Move to start position */
	fprintf(out, "%u -%u moveto\n",
		xpos,
		TOP_BOX_HEIGHT + line*NORMAL_COLUMN_HEIGHT);
	/* Set width */
	fprintf(out, "%u\n", NORMAL_COLUMN_WIDTH);
	draw_pair(out, upperstr, lowerstr, NORMAL_FONT_SIZE, true);
}

/* Draw a column of numbers at the left of the current point */
static void draw_numbers(FILE *out, unsigned int maxnum, bool move_down)
{
	unsigned int i;

	/* Draw title */
	fprintf(out, "-%u 0 rmoveto\n", NORMAL_COLUMN_WIDTH);
	draw_box(out, NORMAL_COLUMN_WIDTH,
		 TOP_BOX_HEIGHT,
		 "Count", NUMBER_FONT_SIZE, ORIENT_VERTICAL, true);
	fprintf(out, "-%u -%u rmoveto\n",
		NORMAL_COLUMN_WIDTH, TOP_BOX_HEIGHT);

	/* Set font */
	fprintf(out, "/%s findfont ", COUNT_NUMBER_FONT);
	fprintf(out, "%u scalefont setfont ", NUMBER_FONT_SIZE);

	if (move_down) {
		fprintf(out, "0 -%u rmoveto\n",	NORMAL_COLUMN_HEIGHT/2);
		/* Draw lines to attach up */
		fprintf(out, "gsave"
			" 0 %u rlineto %u 0 rmoveto 0 -%u rlineto stroke"
			" grestore\n",
			NORMAL_COLUMN_HEIGHT/2,
			NORMAL_COLUMN_WIDTH,
			NORMAL_COLUMN_HEIGHT/2);
	}

	/* Draw every digit H. */
	for (i = 0; i < maxnum; i++) {
		char countstr[INT_CHARS+1];
		sprintf(countstr, "%u", i+1);
		/* Set width */
		fprintf(out, "%u\n", NORMAL_COLUMN_WIDTH);
		draw_pair(out, countstr, "", NUMBER_FONT_SIZE, true);
	}
	/* Move back up to the top. */
	fprintf(out, "0 %u rmoveto\n",
		NORMAL_COLUMN_HEIGHT*maxnum + TOP_BOX_HEIGHT
		+ NORMAL_COLUMN_HEIGHT/2);
}

/* Takes column width from the stack, moves cursor LEFT. */
static void draw_column(FILE *out, 
			const char *title,
			char *top_strings[],
			char *bottom_strings[],
			unsigned int fontsize,
			unsigned int num_counts,
			bool move_down)
{
	unsigned int i;
	unsigned int extra_down;

	/* Duplicate width. */
	fprintf(out, "dup ");

	if (move_down) extra_down = NORMAL_COLUMN_HEIGHT/2;
	else extra_down = 0;

	/* Draw title */
	fprintf(out, "neg 0 rmoveto dup\n");
	__draw_box(out, TOP_BOX_HEIGHT, title,
		   NORMAL_FONT_SIZE, ORIENT_HORIZONTAL, true);
	fprintf(out, "dup neg -%u rmoveto\n",
		TOP_BOX_HEIGHT+extra_down);

	/* Draw every digit H. */
	for (i = 0; i < num_counts; i++) {
		/* Duplicate width. */
		fprintf(out, "dup ");
		draw_pair(out, top_strings[i], bottom_strings[i],
			  fontsize, false);
	}
	/* Pop last width, and move back up to the top. */
	fprintf(out, "pop 0 %u rmoveto\n",
		NORMAL_COLUMN_HEIGHT*num_counts + TOP_BOX_HEIGHT + extra_down);
}

static char *get_time_string()
{
	time_t now;
	char *ret=malloc(sizeof(char) * 50);

	time(&now);
	
	sprintf(ret, "%s", ctime(&now));
	
	return ret;
}
	
#define COUNT_DESCRIP \
	"Description of Choices Counted (NAC = Next Available Candidate)"
static void garnish_counting(unsigned int num_counts, const char *title)
{
	unsigned int i;

	fprintf(counting.out, "/Helvetica findfont ");
	fprintf(counting.out, "%u scalefont setfont ", DESCRIP_FONT_SIZE);
	/* Figure out max string length: answer on stack */
	max_length(counting.out,
		   COUNT_DESCRIP,
		   counting.count_descrip[TOP],
		   counting.count_descrip[BOTTOM],
		   num_counts);

	/* Move to origin. */
	fprintf(counting.out, "0 0 moveto\n");

	/* Takes column width from the stack, moves cursor LEFT. */
	/* Note that draw_column considers pairs above and below the line,
	   and Table 1 considers the pairs to be those within a "box".
	   So TOP and BOTTOM are reversed, and TOP is move "up" one */
	draw_column(counting.out, COUNT_DESCRIP,
		    counting.count_descrip[BOTTOM],
		    counting.count_descrip[TOP]+1,
		    DESCRIP_FONT_SIZE,
		    num_counts,
		    true);
	/* Moves cursor left again */
	draw_numbers(counting.out, num_counts, true);

	/* Draw table title */
	fprintf(counting.out, "/Helvetica findfont ");
	fprintf(counting.out, "%u scalefont setfont ",
		TOP_LEFT_INFO_FONT_SIZE);

	/* Move up a little */
	fprintf(counting.out, "0 %u rmoveto\n", TOP_LEFT_INFO_FONT_SIZE);
	fprintf(counting.out,"gsave (Table I - Counting of the Choices - %s) show grestore\n",
	      get_time_string());

	/* Draw number of votes */
	
	fprintf(counting.out,
		"0 %u rmoveto\n", TOP_LEFT_INFO_FONT_SIZE*3);
	/* mod for cas vac */
	if (counting.num_formals == 0) counting.num_formals = distribution.vacancy_total_ballots;
	fprintf(counting.out,
		"gsave (Number of formal papers: %u."
		"  Number of informal papers: %u.) show grestore\n",
		counting.num_formals, counting.num_informals);

	/* Draw title */
	fprintf(counting.out, "/Helvetica findfont ");
	fprintf(counting.out, "%u scalefont setfont ", TITLE_FONT_SIZE);
	fprintf(counting.out,
		"0 %u rmoveto\n",
		TOP_LEFT_INFO_FONT_SIZE + TITLE_FONT_SIZE*2);
	fprintf(counting.out,
		"gsave"
		" (Scrutiny Sheet for %s - Division of %s) "
		"show grestore\n",
		title, counting.ename);

	for (i = 0; i < num_counts; i++) {
		free(counting.count_descrip[TOP][i]);
		counting.count_descrip[TOP][i] = NULL;
		free(counting.count_descrip[BOTTOM][i]);
		counting.count_descrip[BOTTOM][i] = NULL;
	}
}

#define REMARKS "Remarks"
static void garnish_distibution(unsigned int num_counts, const char *title)
{
	unsigned int i;

	/* Set normal font */
	fprintf(distribution.out, "/Helvetica findfont ");
	fprintf(distribution.out, "%u scalefont setfont ", NORMAL_FONT_SIZE);

	/* Figure out max string length: answer on stack */
	max_length(distribution.out, 
		   REMARKS,
		   distribution.remarks[TOP],
		   distribution.remarks[BOTTOM],
		   num_counts);

	/* We need to be at far right + width of remarks column (on stack) */
	fprintf(distribution.out, "dup %u add 0 moveto\n",
		distribution.remark);
	/* Takes column width from the stack, moves cursor LEFT. */
	draw_column(distribution.out, REMARKS,
		    distribution.remarks[TOP],
		    distribution.remarks[BOTTOM],
		    NORMAL_FONT_SIZE,
		    num_counts,
		    false);

	/* Move to origin. */
	fprintf(distribution.out, "0 0 moveto\n");

	/* Moves cursor left */
	draw_numbers(distribution.out, num_counts, false);

	/* Draw table title */
	fprintf(distribution.out, "/Helvetica findfont ");
	fprintf(distribution.out, "%u scalefont setfont ",
		TOP_LEFT_INFO_FONT_SIZE);
	/* Move up a little */
	fprintf(distribution.out, "0 %u rmoveto\n", TOP_LEFT_INFO_FONT_SIZE);
	fprintf(distribution.out,"gsave (Table II - Distribution of the Effective Votes - %s)"
	      " show grestore\n",
	      get_time_string());

	/* Draw quota calculation */
	if (distribution.quota != 0) {
		fprintf(distribution.out,
			"0 %u rmoveto gsave\n", TOP_LEFT_INFO_FONT_SIZE*3);
		fprintf(distribution.out, "(Quota = ) show\n");
		fprintf(distribution.out,
			"gsave 0 %u rmoveto (   %u) show grestore\n",
			TOP_LEFT_INFO_FONT_SIZE/2+3,
			distribution.num_formals);
		fprintf(distribution.out,
			"gsave  0 -%u rmoveto ( %u+1) show grestore\n",
			TOP_LEFT_INFO_FONT_SIZE/2+3,
			distribution.num_seats);
		fprintf(distribution.out,
			"gsave %u 0 rlineto stroke grestore\n",
			TOP_LEFT_INFO_FONT_SIZE * 5);
		fprintf(distribution.out,
			"%u 0 rmoveto (  + 1 = %u) show grestore\n",
			TOP_LEFT_INFO_FONT_SIZE * 5, distribution.quota);
	}

	/* Draw total for casual vacancy. */
	if (distribution.vacancy_total_votes != 0) {
		fprintf(distribution.out,
			"0 %u rmoveto gsave"
			" (Total votes to be distributed = %u)"
			" show grestore\n",
			TOP_LEFT_INFO_FONT_SIZE*3,
			distribution.vacancy_total_votes);
	}

	/* Draw title */
	fprintf(distribution.out, "/Helvetica findfont ");
	fprintf(distribution.out, "%u scalefont setfont ", TITLE_FONT_SIZE);

	fprintf(distribution.out,
		"0 %u rmoveto\n",
		TOP_LEFT_INFO_FONT_SIZE + TITLE_FONT_SIZE*2);
	fprintf(distribution.out,
		"gsave"
		" (Scrutiny Sheet for %s - Division of %s) "
		"show grestore\n",
		title, distribution.ename);

	for (i = 0; i < num_counts; i++) {
		free(distribution.remarks[TOP][i]);
		distribution.remarks[TOP][i] = NULL;
		free(distribution.remarks[BOTTOM][i]);
		distribution.remarks[BOTTOM][i] = NULL;
	}
}

static void close_postscript(FILE *out)
{
	fputs("%%Trailer\n", out);
	fputs("showpage\n", out);
	fclose(out);
}

void report_end(unsigned int num_counts, const char *title)
{
	garnish_counting(num_counts, title);
	close_postscript(counting.out);
	free(counting.ename);

	garnish_distibution(num_counts, title);
	close_postscript(distribution.out);
	free(distribution.ename);
	
	fclose(distribution.raw);
	fclose(counting.raw);
}

static void append_report(char **string, const char *format, ...)
__attribute__((format(printf,2,3)));

static void append_report(char **string, const char *format, ...)
{
	int space;
	char *ptr;
	va_list arglist;

	va_start(arglist, format);
	space = vsnprintf(NULL, 0, format, arglist);
	/* Old glibc, gives bogus return */
	if (space == -1) space = 1024;
	else space ++;

	if (*string) {
		space += strlen(*string);
		*string = realloc(*string, space);
		ptr = *string + strlen(*string);
	} else {
		ptr = *string = malloc(space);
	}
	vsprintf(ptr, format, arglist);	
	va_end(arglist);
}

void report_informals(unsigned int num_informals)
{
	counting.num_informals = num_informals;
}

void report_quota(unsigned int num_formals,
		  unsigned int num_seats,
		  unsigned int quota)
{
	counting.num_formals = distribution.num_formals = num_formals;
	distribution.num_seats = num_seats;
	distribution.quota = quota;
}

static void draw_number_box(FILE *out, unsigned int count, unsigned int xpos,
			    unsigned int value)
{
	char valstring[INT_CHARS+1];

	sprintf(valstring, "%u", value);
	fprintf(out, "%u -%u moveto\n", xpos,
		TOP_BOX_HEIGHT + count*NORMAL_COLUMN_HEIGHT);
	draw_box(out, NORMAL_COLUMN_WIDTH, NORMAL_COLUMN_HEIGHT,
		 valstring, NUMBER_FONT_SIZE, ORIENT_HORIZONTAL, true);
}

#if 0
static void draw_dual_number_box(FILE *out,
				 unsigned int line,
				 unsigned int xpos,
				 unsigned int upper,
				 int lower)
{
	char upperstr[INT_CHARS+1], lowerstr[INT_CHARS+1];

	/* Skip top number (ie. total) for first line */
	if (line == 0) upperstr[0] = '\0';
	else sprintf(upperstr, "%u", upper);
	sprintf(lowerstr, "%i", lower);

	fprintf(out, "%u -%u moveto\n",
		xpos, TOP_BOX_HEIGHT + line*NORMAL_COLUMN_HEIGHT);
	fprintf(out, "%u\n", NORMAL_COLUMN_WIDTH);
	draw_dual_box(out, upperstr, lowerstr, NUMBER_FONT_SIZE, true);
}
#endif

void report_exhausted(unsigned int count,
		      unsigned int ballots_exhausted,
		      unsigned int votes_exhausted)
{
	distribution.total_exhausted += votes_exhausted;

	/* if this is the first distribution of vacating candidates votes .
	   (i.e. count 0, don't draw the postscript  */ 
	if (count > 0 ) {
		draw_number_box(counting.out, count-1, counting.exhausted,
				ballots_exhausted);
		
		draw_number_pair(distribution.out,
				 distribution.exhausted,
				 count-1,
				 votes_exhausted, distribution.total_exhausted);
		fprintf(counting.raw,"EX:%u:%u\n",count,ballots_exhausted);
		fprintf(distribution.raw,"EX:%u:%u:%u\n",count,votes_exhausted,distribution.total_exhausted);	
	}
}

/* Draw a column with a line down the middle */
static void draw_line(FILE *out, unsigned int line, unsigned int candpos)
{
	fprintf(out, "%u -%u moveto\n",
		candpos*NORMAL_COLUMN_WIDTH,
		TOP_BOX_HEIGHT + line*NORMAL_COLUMN_HEIGHT);

	fprintf(out, "gsave 0 -%u rlineto stroke grestore\n",
		NORMAL_COLUMN_HEIGHT);
	fprintf(out, "gsave %u 0 rmoveto 0 -%u rlineto stroke grestore\n",
		NORMAL_COLUMN_WIDTH, NORMAL_COLUMN_HEIGHT);
	fprintf(out, "gsave 0 setlinewidth %u 0 rmoveto 0 -%u rlineto stroke"
		" grestore\n",
		NORMAL_COLUMN_WIDTH/2, NORMAL_COLUMN_HEIGHT);
}

/* Draw an empty column */
/* SIPL 2011-05-24 This failed with newer versions of Ghostscript
   (and some printers) if fontsize was 0.  In this case,
   the label was always blank.  So now, check
   if fontsize is 0, and if so, just replace it with something
   other than 0.  */
static void draw_empty(FILE *out, unsigned int line, unsigned int candpos,
		       const char *label, unsigned int fontsize)
{
	/* SIPL 2011-05-24 Deal with fontsize of 0. */
	if (fontsize == 0)
          	fontsize = 1;

	/* Move to correct location */
	fprintf(out, "%u -%u moveto\n",
		candpos*NORMAL_COLUMN_WIDTH,
		TOP_BOX_HEIGHT + line*NORMAL_COLUMN_HEIGHT);

	/* Draw lines down left and right side */
	fprintf(out, "gsave 0 -%u rlineto stroke grestore\n",
		NORMAL_COLUMN_HEIGHT);
	fprintf(out, "gsave %u 0 rmoveto 0 -%u rlineto stroke grestore\n",
		NORMAL_COLUMN_WIDTH, NORMAL_COLUMN_HEIGHT);

	/* Move to centre */
	fprintf(counting.out, "%u -%u rmoveto\n",
		NORMAL_COLUMN_WIDTH/2,
		NORMAL_COLUMN_HEIGHT/2);

	/* Figure label height and width, move back half of it. */
	fprintf(out, "/Helvetica findfont ");
	fprintf(out, "%u scalefont setfont ", fontsize);
	fprintf(out, "(%s) dup stringwidth"
		" 2 div neg 2 1 roll 2 div neg 2 1 roll rmoveto ", label);
	/* Draw it */
	fprintf(out, "show\n");
}

void report_ballots_transferred(unsigned int count,
				unsigned int candpos,
				enum cand_status status,
				unsigned int ballots_added)
{
	if (status == CAND_ELECTED || status == CAND_EXCLUDED)
		draw_line(counting.out, count-1, candpos);
	else {
		fprintf(counting.raw,"BT:%u:%u:%u\n",count,candpos,ballots_added);
		draw_number_box(counting.out, count-1,
				candpos*NORMAL_COLUMN_WIDTH,
				ballots_added);
	}
}

/* Draw shading from where their total reaches quota or they are elected*/
/*  static void draw_shading(FILE *out, unsigned int line, unsigned int candpos) */
/*  { */
/*  	fprintf(out, "gsave newpath %u -%u moveto\n", */
/*  		candpos*NORMAL_COLUMN_WIDTH, */
/*  		TOP_BOX_HEIGHT + line*NORMAL_COLUMN_HEIGHT */
/*  		+ NORMAL_COLUMN_HEIGHT/2); */
/*  	fprintf(out, "%u 0 rlineto 0 -%u rlineto -%u 0 rlineto" */
/*  		" 0 %u rlineto 0.8 0.8 0.8 setrgbcolor fill grestore\n", */
/*  		NORMAL_COLUMN_WIDTH, NORMAL_COLUMN_HEIGHT, */
/*  		NORMAL_COLUMN_WIDTH, NORMAL_COLUMN_HEIGHT); */
/*  } */

void report_votes_transferred(unsigned int count,
			      unsigned int candpos,
			      enum cand_status status,
			      int added,
			      unsigned int new_total)
{
	/* No box if they're excluded */
	if (status == CAND_EXCLUDED) {
		draw_empty(distribution.out, count-1, candpos, "", 0);
		return;
	}
	/* ACT EC 19/09/01   No Shading   */
	/* Shade it if they're over quota or elected*/
/*  	if (status == CAND_ELECTED || new_total >= distribution.quota) { */
/*  	        draw_shading(distribution.out, count-1, candpos); */
/*  	} */
	 
	fprintf(distribution.raw,"VT:%u:%u:%i:%u\n",count,candpos,added,new_total);
	draw_number_pair(distribution.out,
			 candpos*NORMAL_COLUMN_WIDTH,
			 count-1,
			 added, new_total);
}

void report_totals(unsigned int count,
		   unsigned int votes,
		   unsigned int ballots)
{
	char string[INT_CHARS+1];

	draw_number_box(counting.out, count-1, counting.counted, ballots);
	/* output raw data */
	fprintf(counting.raw,"TT:%u:%u\n",count,  ballots);

	sprintf(string, "%u",
		votes + distribution.total_loss +distribution.total_exhausted);
	/* Move to start position */
	fprintf(distribution.out, "%u -%u moveto\n",
		distribution.total,
		TOP_BOX_HEIGHT + (count-1)*NORMAL_COLUMN_HEIGHT);

	/* Set font */
	fprintf(distribution.out, "/Helvetica findfont ");
	fprintf(distribution.out, "%u scalefont setfont ", NORMAL_FONT_SIZE);

	/* Set width */
	fprintf(distribution.out, "%u\n", NORMAL_COLUMN_WIDTH);
	draw_pair(distribution.out, "", string, NORMAL_FONT_SIZE, true);
	/* output raw data */
	fprintf(distribution.raw,"TT:%u:%s\n",count, string);


	
}

void report_transfer(unsigned int count,
		     struct fraction value,
		     unsigned int votes_transferred)
{
	char valstring[INT_CHARS + sizeof(" / ") + INT_CHARS];

	/* If denominator == 1, skip it */
	if (value.denominator == 1)
		sprintf(valstring, "%lu", value.numerator);
	else
		sprintf(valstring, "%lu / %lu",
			value.numerator, value.denominator);

	fprintf(counting.out, "%u -%u moveto\n",
		counting.transfer_value,
		TOP_BOX_HEIGHT + (count-1)*NORMAL_COLUMN_HEIGHT);
	draw_box(counting.out, FRACTION_COLUMN_WIDTH, NORMAL_COLUMN_HEIGHT,
		 valstring, NUMBER_FONT_SIZE, ORIENT_HORIZONTAL, true);

	draw_number_box(counting.out, count-1, counting.to_table2, 
			votes_transferred);
	/* report transfer value to raw data stream */
	fprintf(counting.raw,"TV:%u:%s\n",count,valstring);
	/* report votes transferred to table 2 to raw data stream */
	fprintf(counting.raw,"VT:%u:%u\n",count,votes_transferred);
}

void report_distribution(unsigned int count, const char *name)
{
	append_report(&distribution.remarks[TOP][count-1],
		      "%s's votes distributed.  ", name);
	append_report(&counting.count_descrip[BOTTOM][count-1],
		      "NAC after %s", name);
	/* SIPL 2011-06-16 Added count to output, and also
	   output to table 1. */
	fprintf(counting.raw,"DS:%u:%s\n",count,name);
	fprintf(distribution.raw,"DS:%u:%s\n",count,name);
}

void report_majority(unsigned int count, unsigned int majority)
{
	if (previous_count != count ||
	    previous_majority != majority) {
		append_report(&distribution.remarks[BOTTOM][count-1],
			      "Majority %u.  ", majority);
		/* SIPL 2011-06-16 Added count to output. */
		fprintf(distribution.raw,"MJ:%u:%u\n",count,majority);
	
	}
	previous_count = count;
	previous_majority = majority;
}

/* populate relevant data structure (garnish will do the actual reporting) */
void report_vacancy_total_votes(unsigned int total)
{
	distribution.vacancy_total_votes = total;
}

/* populate relevant data structure (garnish will do the actual reporting) */
void report_vacancy_total_ballots(unsigned int total)
{
	distribution.vacancy_total_ballots = total;
}

/* What previous count did these papers come from? */
void report_distrib_from_count(unsigned int count, unsigned int prev_count)
{
	if (counting.count_descrip[TOP][count-1] == NULL) {
		append_report(&counting.count_descrip[TOP][count-1],
			      "On Papers at Count %u", prev_count);
		fprintf(counting.raw,"PS:%u:",count);
			
	} else 
		append_report(&counting.count_descrip[TOP][count-1],
			      ",%u", prev_count);
	
	fprintf(counting.raw,"%u,",prev_count);

}

void report_lost_or_gained(unsigned int count, int gained)
{
	distribution.total_loss -= gained;
	/* We report the number LOST, not gained */
	draw_number_pair(distribution.out,
			 distribution.loss_gain,
			 count-1,
			 -gained,
			 distribution.total_loss);
	fprintf(distribution.raw,"LG:%u:%i:%i\n",count,-gained, distribution.total_loss);
}

void report_elected(unsigned int count, unsigned int candpos)
{
	draw_empty(counting.out, count-1, candpos, "ELECTED",
		   NORMAL_FONT_SIZE/2);
}

void report_excluded(unsigned int count, unsigned int candpos)
{
	draw_empty(counting.out, count-1, candpos, "EXCLUDED",
		   NORMAL_FONT_SIZE/2);
}

void report_pending(unsigned int count, const char *name)
{
	append_report(&distribution.remarks[BOTTOM][count-1],
		      " %s elected %u.  ", name, get_order_elected());
	fprintf(distribution.raw,"EL:%u:%s:%u\n",count,name, get_order_elected());
}

void report_tiebreak(unsigned int count, const char *reason, const char *name)
{
	append_report(&distribution.remarks[BOTTOM][count-1],
		      "%s chosen for %s tiebreak.  ", name, reason);
	fprintf(distribution.raw,"TB:%u:%s:%s\n",count,reason, name);
}

void report_partially_excluded(unsigned int count, const char *name)
{
	append_report(&distribution.remarks[BOTTOM][count-1],
		      "%s partially excluded.  ", name);
	
	fprintf(distribution.raw,"PE:%u:%s\n",count, name);
}

void report_fully_excluded(unsigned int count, const char *name)
{
	append_report(&distribution.remarks[BOTTOM][count-1],
		      "%s fully excluded.  ", name);
	fprintf(distribution.raw,"FE:%u:%s\n",count, name);
}





