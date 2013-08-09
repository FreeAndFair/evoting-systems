#ifndef _CREATETABLES_H
#define _CREATETABLES_H
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

/* This file contains table and database create and drop functions. */
#include <libpq-fe.h>
#ifndef HASH_BITS
#define HASH_BITS 160
#endif

extern void create_database(PGconn *conn, const char *name);
extern void drop_database(PGconn *conn, const char *name);

extern void create_ballot_content_tables(PGconn *conn);
extern void create_candidate_table(PGconn *conn);
extern void create_party_table(PGconn *conn);
extern void create_paper_tables(PGconn *conn);
extern void create_entry_tables(PGconn *conn);
extern void create_duplicate_entry_table(PGconn *conn); 
extern void create_electorate_table(PGconn *conn);
extern void create_batch_table(PGconn *conn);
extern void create_batch_history_table(PGconn *conn);
extern void create_polling_place_table(PGconn *conn);
extern void create_barcode_table(PGconn *conn);
extern void create_server_parameter_table(PGconn *conn);
extern void create_robson_rotation_table(PGconn *conn,
					 unsigned int number_of_seats);
extern void create_confirmed_vote_tables(PGconn *conn);

/* Test routine to drop and recreate an entire database */
extern PGconn *clean_database(const char *name);
extern void create_last_result_table(PGconn *conn);
/* Election Night System tables */
extern void create_preference_summary_table(PGconn *conn);
extern void create_vote_summary_table(PGconn *conn);
extern void create_scrutiny_tables(PGconn *conn);
#endif /*_CREATETABLES_H*/
