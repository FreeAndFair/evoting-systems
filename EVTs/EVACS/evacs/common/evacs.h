#ifndef _EVACS_H
#define _EVACS_H
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

/* This file contains global definitions, used throughout EVACS */
#include <limits.h>
#include <stdio.h>
#include <stdarg.h>
#include <sys/types.h>
#include <stdbool.h>

/* C trick to stringize a constant (expand to the number first) */
#define _STRINGIZE(x) #x
#define STRINGIZE(x) _STRINGIZE(x)

/* Useful macro which defines max size of a string containing an int.
   UINT has a U at the end, but int may have - at the front, so the
   size is correct. */
#define INT_CHARS (sizeof(STRINGIZE(UINT_MAX)))

/* This is the maximum number of electorate seats. */
#define MAX_ELECTORATE_SEATS 7

/* Maximum preference number is 99 */
#define PREFNUM_MAX 99
/* maximum number of electorates */
#define MAX_ELECS 3
/* maximum number of groups per electorate */
#define MAX_GROUPS 12

/* number of (ASCII) digits to describe one preference */
#define DIGITS_PER_PREF 6

#define SERVER_ADDRESS "192.168.1.75"
 
#ifndef SERVER_PORT
#define SERVER_PORT 8080
#endif

/* These are added for the setup phase - display ballot papers*/
#define TEST_SERVER_ADDRESS "localhost"
#define TEST_SERVER_PORT 8080


struct electorate
{
	/* Non-NULL if this is part of a list. */
	struct electorate *next;

	unsigned int code;
	unsigned int num_seats;
	/* nul-terminated string hangs off end of structure */
	char name[0];
};

struct polling_place
{
	unsigned int code;
	/* nul-terminated string hangs off end of structure */
	char name[0];
};

struct preference
{
	unsigned int group_index;
	unsigned int db_candidate_index;
	unsigned int prefnum;
};

/* Preference set used in voting */
struct preference_set
{
	unsigned int paper_version;
	unsigned int num_preferences;
	struct preference candidates[PREFNUM_MAX];
};

/* common functions in evacs.c */

/* current username */
extern char *get_operator_id(void);

/* Set your own bailout function */
extern void set_bailout(void (*bailoutfunc)(const char *fmt, va_list ap)
			__attribute__((noreturn)));

/* Call the bailout function */
extern void bailout(const char *fmt, ...)
__attribute__((noreturn, format (printf,1,2)));
extern char *vsprintf_malloc(const char *fmt, va_list arglist);
extern char *sprintf_malloc(const char *fmt, ...)
     __attribute__ ((format(printf,1,2)));
extern char *fgets_malloc(FILE *stream);

extern void create_directory(mode_t mode,const char *fmt, ...)
     __attribute__ ((format(printf,2,3)));
extern void copy_file(const char *source_file,const char *target_file);

/* unpack a string of Hexlets into a preference structure */
extern struct preference_set *unpack_preferences(const char *preference_list);

/* generate a string of Hexlets representing a set of preferences - user must free */
extern char *preference_string(struct preference_set *vote);

/* generate an ASCII timestamp - user must free */
extern char *generate_timestamp(void);

/* generate an ASCII timestamp - user must free */
extern char *generate_sortable_timestamp(void);

/* generate a batch number string representing an electronic batch number - user must free */
extern char *get_batch_number_string(const int elec,const int pp);
#endif /*_EVACS_H*/

