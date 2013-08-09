#ifndef _FIND_ERRORS_H
#define _FIND_ERRORS_H
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

/* This file contains definitions for entries, papers and batches with
   errors annotated */
#include "batch.h"

/* symbolic error codes for entry errors */
enum entry_error
{
	ENTRY_ERR_IGNORED,
	ENTRY_ERR_UNENTERED,
	ENTRY_ERR_KEYSTROKE,
	ENTRY_ERR_INFORMAL,
	ENTRY_ERR_MISSING_NUM,
	ENTRY_ERR_DUPLICATED_NUM,
	ENTRY_ERR_CORRECTED,
	ENTRY_ERR_CORRECT,
	ENTRY_ERR_INVALID_BATCH_APPROVAL
};


struct entry_with_error
{
	/* Non-NULL if this is part of a list. */
	struct entry_with_error *next;

	/* The error code */
        enum entry_error error_code;

	/* The entry itself. */
	struct entry_info e;

	/* Actual preferences hang off end */
	struct preference preferences[0];
};

struct paper_with_error
{
	/* The error code for the paper as a whole */
        enum entry_error error_code;
	
	/* Actual information about this paper */
	struct paper_info p;

	/* Pointer to linked list of entries */
	struct entry_with_error *entries;
};

struct batch_with_error
{
	struct batch_info b;

	/* Papers array hangs off end */
	struct paper_with_error papers[0];
};

extern int match_active_entries(PGconn *conn,
				char *electorate_name,
				int paper_id); 
extern struct batch_with_error *find_errors_in_batch(PGconn *conn,
                                                     const struct batch *b,
                                                 const char *electorate_name);
extern struct paper_with_error find_errors_in_paper(PGconn       *conn,
                                                    const struct paper *paper,
						    unsigned int paper_index,
                                                    unsigned int  batch_number,
						    unsigned int batch_size,
                                                const char *electorate_name);
extern void free_batch_with_error(struct batch_with_error *);
extern bool compare_entries(const struct entry *head, 
			    const struct entry *entry);

extern char *get_error_string(enum entry_error error_code);

#endif /* _FIND_ERRORS_H */
