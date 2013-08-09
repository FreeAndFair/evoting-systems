#ifndef _DATABASE_H
#define _DATABASE_H
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

/* This file contains common database access routines, used in
   election setup, polling place setup, voting server, data entry,
   data correction and counting. */

#include <stdbool.h>
#include <libpq-fe.h>

#ifndef DATABASE_NAME
#define DATABASE_NAME "evacs"
#endif

/* Return NULL on failure. */
extern struct polling_place *get_polling_place(PGconn *conn,
					       const char *ppname);

/* Database access functions: call free_electorates after get_electorates. */
extern struct electorate *get_electorates(PGconn *conn);
extern void free_electorates(struct electorate *);


/* See SQL docs for the format of definition. */
extern PGconn *connect_db(const char *name);
extern PGconn *connect_db_port(const char *name, const char *port_number);
extern PGconn *connect_db_host(const char *name, const char *host);

extern void create_table(PGconn *conn, const char *name, const char *def);
extern void create_index(PGconn *conn,const char *table_name,
			 const char *column_names,const char *index_name);
extern void create_sequence(PGconn *conn,const char *sequence_name);
extern void drop_table(PGconn *conn, const char *name);
extern void drop_sequence(PGconn *conn, const char *name);
extern void begin(PGconn *conn);
extern void commit(PGconn *conn);
extern void rollback(PGconn *conn);
extern unsigned int insert(PGconn *conn, const char *table_name,const char *values);
extern int copy_table(const char *table_name,
		PGconn *source_conn,PGconn *target_conn);
extern int copy_selection(PGresult *result,
			   const char *table_name,PGconn *target_conn);
extern PGresult *SQL_query(PGconn *conn,const char *fmt, ...)
     __attribute__ ((format(printf,2,3)));
extern unsigned int SQL_command(PGconn *conn,const char *fmt, ...)
     __attribute__ ((format(printf,2,3)));
extern unsigned int SQL_command_nobail(PGconn *conn,const char *fmt, ...)
     __attribute__ ((format(printf,2,3)));
extern char *SQL_singleton(PGconn *conn,const char *fmt, ...);
extern bool SQL_singleton_bool(PGconn *conn,const char *fmt, ...);
extern int SQL_singleton_int(PGconn *conn,const char *fmt, ...);
extern char *eq_malloc(char *s);
extern int get_seq_nextval(PGconn *conn,const char *seq_name);
extern int get_seq_currval(PGconn *conn,const char *seq_name);
extern unsigned int SQL_select(PGconn *conn,PGresult **result,
			       unsigned int *row_num,const char *query, ...);

#endif /*_DATABASE_H*/










