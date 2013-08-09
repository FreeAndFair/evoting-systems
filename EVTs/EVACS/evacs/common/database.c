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
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <common/evacs.h>
#include <common/barcode.h>
/*#include <common/safe.h>*/

#include "database.h"

/* DDSv1A-3.2.1: Get Polling Places */
/* resolves a polling place code from a polling place name */
struct polling_place *get_polling_place(PGconn *conn, const char *ppname)
{
	PGresult *result;
	struct polling_place *pp;

	/* SIPL 2011-09-02 An extra column has been added to polling_place.
	   This code was "SELECT *". Now select only the columns needed. */
	result = SQL_query(conn,
			   "SELECT code, name from polling_place "
			   "WHERE name = '%s';",
			   ppname);
	if (PQntuples(result) == 0) {
		PQclear(result);
		return NULL;
	}

	pp = malloc(sizeof(*pp) + PQgetlength(result, 0, 1)+1);
	pp->code = atoi(PQgetvalue(result, 0, 0));
	strcpy(pp->name, PQgetvalue(result, 0, 1));

	PQclear(result);
	return pp;
}

/* DDSv1A-3.1.2: Get Electorates */
struct electorate *get_electorates(PGconn *conn)
{
	PGresult *result;
	struct electorate *elec = NULL, *tmp;
	unsigned int i,num_rows;

	result = SQL_query(conn,
			   "SELECT code,  name, seat_count "
			   "FROM electorate ORDER BY code;");
	
	if ((num_rows = PQntuples(result)) == 0) {
		PQclear(result);
		return NULL;
	}

	for (i = 0; i < num_rows; i++) {
		/* We need to know length of name to know how much storage to
		   allocate */
		tmp = malloc(sizeof(*tmp) + PQgetlength(result, i, 1)+1);
		if (!tmp) {
			/* Out of memory */
			free_electorates(elec);
			PQclear(result);
			return NULL;
		}

		tmp->code = atoi(PQgetvalue(result, i, 0));
		strcpy(tmp->name, PQgetvalue(result, i, 1));
		tmp->num_seats = atoi(PQgetvalue(result, i, 2));
		tmp->next = elec;
		elec = tmp;
	}

	PQclear(result);
	return elec;
}

void free_electorates(struct electorate *elec)
{
	while (elec) {
		struct electorate *next;

		next = elec->next;
		free(elec);
		elec = next;
	}
}
	


char *eq_malloc(char *s)
     /*
       Return s with any single quotes replaced with a pair of
       single quotes.
       
       NOTE: This function allocates memory that must be freed by the
       calling function.
     */
{
        char tmp_s[strlen(s)*2+1];
	char *startp=tmp_s,*sp=s,*quotep;
	int len;

	while ((quotep = strchr(sp,'\''))) {
	        len = quotep - sp + 1;
		strncpy(startp,sp,len);
		startp += len;
		*startp++ = '\'';   /* Insert extra quote */
		sp = quotep + 1;
	}
	
	strcpy(startp,sp);  /* copy (rest) of string */
	sp = (char *)malloc(strlen(tmp_s)+1);
	strcpy(sp,tmp_s);
	
	return (sp);
}

PGconn *connect_db(const char *name)
{
	return connect_db_port(name, NULL);
}

PGconn *connect_db_port(const char *name, const char *port_number)
{
        PGconn *conn;
 	conn = PQsetdb(NULL, port_number, NULL, NULL, name);
	if (PQstatus(conn) != CONNECTION_OK) {
		PQfinish(conn);
		return NULL;
	}
	return conn;
}
PGconn *connect_db_host(const char *name, const char *hostname)
{
        PGconn *conn;
 	conn = PQsetdb(hostname, NULL, NULL, NULL, name);
	if (PQstatus(conn) != CONNECTION_OK) {
		PQfinish(conn);
		return NULL;
	}
	return conn;
}
      
static PGresult *run_SQL(PGconn *conn, bool bail_on_error,
			 const char *fmt,va_list arglist)
     /*
       Execute the query against the database open on conn.
       
       Bailout if a fatal error or bad response is returned and
       bail_on_error is true.

       Should NOT be called directly. Use SQL_query or SQL_command
       interface ONLY!
     */
{
        char *sql;

	PGresult *result;
	ExecStatusType result_status;
	sql = vsprintf_malloc(fmt,arglist);

	result = PQexec(conn,sql);
	result_status = PQresultStatus(result);
	
	if ( bail_on_error && result_status != PGRES_COMMAND_OK &&
	     result_status != PGRES_TUPLES_OK)
	        bailout("SQL command %s failed: %s (%s)\n",
			sql, PQresStatus(PQresultStatus(result)),
			PQresultErrorMessage(result));
	free(sql);
	return(result);
}

static unsigned int SQL_cmd(PGconn *conn,bool bail_on_error,
			      const char *fmt,va_list arglist)
     /*
       Run the SQL command. Return the number of rows effected.
       This number will be zero if the command was not an INSERT
       UPDATE or DELETE.
     */
{
	PGresult *result;
	unsigned int num_rows;

	result = run_SQL(conn,bail_on_error,fmt,arglist);
 
	num_rows = (unsigned int)atoi(PQcmdTuples(result));
  
	/* Free result structure */
	PQclear(result);

	return(num_rows);
}

extern unsigned int SQL_command(PGconn *conn,const char *fmt, ...)
     __attribute__ ((format(printf,2,3)));

unsigned int SQL_command(PGconn *conn,const char *fmt, ...)
{
        va_list arglist;
	unsigned int num_rows;

	va_start(arglist,fmt);
	num_rows = SQL_cmd(conn,true,fmt,arglist);
	va_end(arglist);

	return(num_rows);
}

extern unsigned int SQL_command_nobail(PGconn *conn,const char *fmt, ...)
     __attribute__ ((format(printf,2,3)));

unsigned int SQL_command_nobail(PGconn *conn,const char *fmt, ...)
{
        va_list arglist;
	unsigned int num_rows;

	va_start(arglist,fmt);
	num_rows = SQL_cmd(conn,false,fmt,arglist);
	va_end(arglist);

	return(num_rows);
}

/* Create a table in a database */
void create_table(PGconn *conn, const char *name, const char *def)
{
	SQL_command(conn,"CREATE TABLE %s ( %s );",name,def);
}

/* Create an index on an existing table */
void create_index(PGconn *conn,const char *table_name,
		  const char *column_names,const char *index_name)
{
        SQL_command(conn,"CREATE INDEX %s on %s(%s);",
		    index_name,table_name,column_names);
}

/* Create a sequence with default starting, minimum and maximum values */
void create_sequence(PGconn *conn,const char *sequence_name)
{
        SQL_command(conn,"CREATE SEQUENCE %s;",sequence_name);
}

/* Drop a table from a database */
void drop_table(PGconn *conn, const char *name)
{
	SQL_command_nobail(conn,"DROP TABLE %s;",name);
}

/* Drop a sequence from a database */
void drop_sequence(PGconn *conn, const char *name)
{
	SQL_command_nobail(conn,"DROP SEQUENCE %s;",name);
}

void begin(PGconn *conn)
{
        SQL_command(conn,"BEGIN WORK;");
}

void commit(PGconn *conn)
{
        SQL_command(conn,"COMMIT WORK;");
}

void rollback(PGconn *conn)
{
	SQL_command(conn,"ROLLBACK WORK;");
}

unsigned int insert(PGconn *conn, const char *table_name,const char *values)
{
        return(SQL_command(conn,"INSERT INTO %s VALUES ( %s );",
		    table_name,values));
}

PGresult *SQL_query(PGconn *conn,const char *fmt, ...)
     /*
       Run the SQL query. Return the pointer to the PGresult structure.
     */
{
        va_list arglist;
	PGresult *result;

	va_start(arglist,fmt);
	result = run_SQL(conn,true,fmt,arglist);
	va_end(arglist);

	return(result);
}

static char *SQL_single(PGconn *conn,const char *fmt,va_list arglist)
     /*
       Run the SQL query. Return the pointer to the first field of the
       first row returned. This memory is malloced so the caller must
       free. 

       It will bail if more that one row is returned from the
       query, or if zero or more than one field is returned.

       If zero rows are returned the function will return NULL.

       This should not be called directly, use SQL_singleton or 
       SQL_singleton_int.
     */
{
        char *ret=NULL;
	PGresult *result;
	unsigned int num_rows, num_fields;

	result = run_SQL(conn,true,fmt,arglist);

	num_rows = PQntuples(result);
	num_fields = PQnfields(result);

	if ( num_rows > 1) 
	        bailout("SQL_single %s returned %d rows!\n",
			fmt,num_rows);

	if (num_fields != 1) /* Should be one field */ 
	        bailout("SQL_single %s returned %d fields!\n",
			fmt,num_fields);

	if (num_rows == 1)
	  ret = strdup(PQgetvalue(result,0,0));

	PQclear(result);

	return(ret);
}

char *SQL_singleton(PGconn *conn,const char *fmt, ...)
     /*
       Run the SQL query and return the single field text result from the
       one row returned. Return NULL if no row returned.
     */
{
        va_list arglist;
	char *ret;

	va_start(arglist,fmt);
	ret = SQL_single(conn,fmt,arglist);
	va_end(arglist);

	return(ret);
}

bool SQL_singleton_bool(PGconn *conn,const char *fmt, ...)
     /*
       Run the SQL query and return the single field boolean result from the
       one row returned. 

       NOTE This function returns false if no row returned from query.
       Use when you a certain a row exists!
     */
{
        va_list arglist;
	char *ret;
	char ret_val;

	va_start(arglist,fmt);
	ret = SQL_single(conn,fmt,arglist);
	va_end(arglist);

	if (ret == NULL)
	  return(false);

	ret_val = *ret;
	free(ret);

	if (ret_val == 't')
		return(true);
	else
		return(false);
}

int SQL_singleton_int(PGconn *conn,const char *fmt, ...)
     /*
       Run the SQL query and return the single field integer result from the
       one row returned. Return -1 if no row returned from query.
     */
{
        va_list arglist;
	char *ret;
	int ret_val;

	va_start(arglist,fmt);
	ret = SQL_single(conn,fmt,arglist);
	va_end(arglist);

	if (ret == NULL)
	  return(-1);

	ret_val = atoi(ret);
	free(ret);

	return(ret_val);
}

unsigned int SQL_select(PGconn *conn,PGresult **result,unsigned int *row_num,
			const char *query, ...)
     /*
       Run the SQL query and return pointers to values returned, if found.
       The query must be contained entirely in the query string, no additional
       parameters may be passed like the SQL_query() function.

       The function returns the number of rows left to be returned by the
       query, including the current one. So the first call can be used to
       return the total number of rows that will be returned by the select.
       A zero return on the first call means that no rows were returned by the
       query.

       On second, and subsequent calls to this function the pointer to the
       result structure is passed back in so that data for the other rows
       may be retrieved.

       If is the programmers responsibility to ensure that there are a 
       sufficient number of parameters to receive the returned results.
       Each parameter MUST be of type char ** as a pointer to a char pointer
       is returned in each. If the number of parameters falls short of the
       actual number of fields returned by the SELECT then unpredictable
       results will occur! Conversely if the number of fields
       returned is less than the number of parameters, the additional 
       parameters will be returned unchanged.

       When this function returns 0 the values returned in each parameter
       will be returned unchanged. 

      */
{
        unsigned int num_rows=0,num_fields=0,field;
	va_list arglist;

	if ( *result == NULL ) {  /* First execution */
  	        *result = run_SQL(conn,true,query,NULL);
		*row_num = 0;
	}

	num_rows = PQntuples(*result);
	num_fields = PQnfields(*result);
	
	if ( *row_num >= num_rows ) /* rows exhausted? */
	        return(0);

	va_start(arglist,query);
	for (field=0;field < num_fields; field++)
	        *(va_arg(arglist,char **)) = 
		  PQgetvalue(*result,*row_num,field);
	va_end(arglist);

	(*row_num)++;

	return(num_rows - *row_num + 1);
}

int copy_selection(PGresult *result,
		    const char *table_name,PGconn *conn)
     /*
       Copy the result of the query on the source table to the target table.

       The table MUST exist in both databases and be defined with the
       same number and type of columns, in the same order. The target
       table can already contain rows, but it is the callers responsibility
       to ensure copying the rows from the source table will not violate
       any integrity constraints on the target table.

       SQL errors will cause this function to abort via a call to bailout.

       The following OID values were obtained from the Postgres
       header file /usr/include/pgsql/catalog/pg_type.h since they
       were not documented in the Postgres text on hand.
       
       Only the OID values for the types we are using have been included.
       Any unknown OID value will cause this function to bailout.

       The number of rows copied is return by the function.
     */

#define BOOL 16
#define INT4 23
#define INTEGER INT4
#define TEXT 25
#define INT_ARRAY 1007
#define BIT 1560
{
        unsigned int num_rows,num_fields;
	unsigned int row,field;
	Oid field_type;
	char *values=NULL,*newvalues,*qs;

	num_rows = PQntuples(result);   /* Find the number of rows returned */
	begin(conn);
	for (row=0;row<num_rows;row++) {
		num_fields = PQnfields(result); /* Find the number of fields */
		for (field=0;field<num_fields;field++) {
		        field_type = PQftype(result,field);
			switch (field_type) {
			case BIT:
			case BOOL:
			case INT_ARRAY:
			case TEXT:
			        if ( values == NULL )
				        values = sprintf_malloc("'%s'",
						 eq_malloc(PQgetvalue(
						           result,row,field)));
				else {
				        newvalues = sprintf_malloc("%s,'%s'",
						    values,
					      	    qs=eq_malloc(PQgetvalue(
						    result,row,field)));
					free(qs);
					free(values);
					values = newvalues;
				}
				break;
			case INTEGER:
			        if ( values == NULL )
				        values = strdup(PQgetvalue(
							    result,row,field));
				else {
				        newvalues = sprintf_malloc("%s,%s",
						    values,
					            PQgetvalue(
						    result,row,field));
					free(values);
					values = newvalues;
				}
			  break;
			default:
			  bailout("Unhandled data type in copy_table. "
				  "OID = %d.\n",field_type);
			}
		}
		insert(conn,table_name,values);  /* target db */
		free(values);
		values = NULL;
	}
	commit(conn);
	return(num_rows);
}

int copy_table(const char *table_name,
		       PGconn *source_conn,PGconn *target_conn)
     /*
       Copy whole table from one database to another. The table must exist
       in both databases with the same definition. 
     */

{
        int num_rows;
	PGresult *result;

	/* SELECT everything into result*/
	result = SQL_query(source_conn,"SELECT * FROM %s;",table_name);
	/* Copy result to target table on target database */
	num_rows = copy_selection(result,table_name,target_conn);
	/* Clear the result */
	PQclear(result);

	return(num_rows);
}

int get_seq_nextval(PGconn *conn,const char *seq_name)
     /*
       Return the next value of a sequence.
     */
{
        int nextval;

	nextval = SQL_singleton_int(conn,"SELECT NEXTVAL('%s');",seq_name);

	if (nextval == -1)
  	        bailout("Could not obtain next value "
			"of sequence %s.\n",seq_name);

	return(nextval);
}

int get_seq_currval(PGconn *conn,const char *seq_name)
     /*
       Return the current value of a sequence.
       Returns minus 1 if the current value of the sequence is not yet
       defined in this session.
     */
{
	return(SQL_singleton_int(conn,"SELECT CURRVAL('%s');",seq_name));
}

