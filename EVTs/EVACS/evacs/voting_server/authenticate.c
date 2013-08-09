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

/* This CGI is invoked by the client to authenticate the barcode and
   map it to the electorate */
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <stdbool.h>
#include <libpq-fe.h>
#include <common/rotation.h>
#include <common/barcode.h>
#include <common/barcode_hash.h>
#include <common/database.h>
#include <common/http.h>
#include "voting_server.h"
#include "cgi.h"

struct barcode_hash_entry
{
	unsigned int ecode;
	unsigned int ppcode;
	bool used;
	char barcodehash[HASH_BITS + 1];
};

/* DDS3.2.4: Get Barcode Hash Table */
/* Returns electorate code, or NULL if not found */
static struct barcode_hash_entry *get_bhash_table(PGconn *conn,
						  const char *barcodehash)
{
	struct barcode_hash_entry *ret=NULL;
	PGresult *result=NULL;

	result = SQL_query(conn,
			   "SELECT electorate_code,polling_place_code, used "
			   "FROM barcode "
			   "WHERE hash = '%s';",barcodehash);
	
	if (PQntuples(result) >= 1) {
	  ret = malloc(sizeof(*ret));
	  ret->ecode = atoi(PQgetvalue(result,0,0));
	  ret->ppcode = atoi(PQgetvalue(result,0,1));
	  /* Booleans are either "t" or "f" */
	  ret->used = (PQgetvalue(result,0,2)[0] == 't');
	  strcpy(ret->barcodehash,barcodehash);
	}
	PQclear(result);

	return ret;
}

/* SIPL 2011-06-22: Support split groups.*/
/* DDS????: Get Ballot Contents */
static struct http_vars *get_ballot_contents(PGconn *conn,unsigned int ecode,
					     struct http_vars *vars)
{
        PGresult *result;
	unsigned int num_groups,group;
	/* SIPL 2011-06-22: Support split groups.*/
	unsigned num_splits,split_index_base,split_index;

	result = SQL_query(conn,
			   "SELECT party_index,count(index) FROM candidate "
			   "WHERE electorate_code = %u "
			   "GROUP BY party_index;",ecode);

	if ( (num_groups = PQntuples(result)) == 0 )
	  bailout("get_ballot_contents failed. "
		  "No groups found for this electorate.\n");

	/* SIPL 2011-06-22 The following calculation allocates space
	   for 3 + 1 + num_groups + 1 variables:
	   3:             pre-existing values (see create_response() below)
	   1:             number of groups "num_groups"
	   num_groups:    "groupX" for X = 0 to num_groups - 1
	   1:             NULL values at end
	*/

	vars = realloc(vars, sizeof(*vars) * (3 + 1 + num_groups + 1));

	vars[3].name = strdup("num_groups");
	vars[3].value = sprintf_malloc("%u", num_groups);

	for (group=0;group<num_groups;group++) {
	  vars[group+4].name = sprintf_malloc("group%s",PQgetvalue(
							 result,group,0));
	  vars[group+4].value = strdup(PQgetvalue(result,group,1));
	}
	vars[group+4].name = vars[group+4].value = NULL;

	PQclear(result);

	/* SIPL 2011-06-22: Now add any details about split groups. */
	/* Fetch all split data. Note ORDER BY clause, required to
	   ensure splitX variables are in sequence. */
	result = SQL_query(conn,
			   "SELECT party_index,physical_column_index,"
			   "candidate_count FROM column_splits "
			   "WHERE electorate_code = %u "
			   "ORDER BY party_index, physical_column_index;",
			   ecode);
	num_splits = PQntuples(result);

	if ( num_splits == 0 ) {
		/* No more to be done. */
		PQclear(result);
		return vars;
	}

	/* SIPL 2011-06-22 The following calculation allocates space
	   for (3 + 1 + num_groups) + 1 + num_splits + 1 variables:
	   (3 + 1 + num_groups):  as above (i.e., not including NULL value)
	   1:                     number of split data elements "num_splits"
	   num_splits:            "splitX" for X = 0 to num_splits - 1
	   1:                     NULL values at end

	   Example of split values:
	    party_index physical_column_index candidate_count
		1		0		3
		1		1		3
	   encoded as follows:
	   split0=1,3
	   split1=1,3

	   There's no need to send physical_column_index values, as long
	   as the data is sent in lexicographic order (as achieved
	   by the ORDER BY clause in the query).
	*/
	vars = realloc(vars, sizeof(*vars) *
		       (3 + 1 + num_groups + 1 + num_splits + 1));
	/* Index of next array location in which to store data.
	   Note: we reuse the previous "last" entry in which NULLs
	   were stored above. */
	split_index_base = 3 + 1 + num_groups;
	vars[split_index_base].name = strdup("num_splits");
	vars[split_index_base].value = sprintf_malloc("%u", num_splits);
	split_index_base++;

	for (split_index = 0; split_index < num_splits; split_index++) {
		vars[split_index_base + split_index].name =
			sprintf_malloc("split%u",split_index);
		vars[split_index_base + split_index].value =
			sprintf_malloc("%s,%s",
				       PQgetvalue(result,split_index,0),
				       PQgetvalue(result,split_index,2));
	}
	/* Put NULL entry back at the new end. */
	vars[split_index_base+split_index].name =
		vars[split_index_base+split_index].value = NULL;

	PQclear(result);
	return vars;
}

/* Send the electorate and ballot contents */
static struct http_vars *create_response(PGconn *conn, struct electorate *elec)
{
	struct http_vars *vars;

	/* Start with the electorate information */
	vars = malloc(sizeof(*vars) * 3);
	vars[0].name = strdup("electorate_name");
	vars[0].value = strdup(elec->name);
	vars[1].name = strdup("electorate_code");
	vars[1].value = sprintf_malloc("%u", elec->code);
	vars[2].name = strdup("electorate_seats");
	vars[2].value = sprintf_malloc("%u", elec->num_seats);

	/* Get the ballot contents stuff. */
	return get_ballot_contents(conn, elec->code,vars);
}

/* DDS3.2.3: Authenticate */
int main(int argc, char *argv[])
{
	struct http_vars *vars;
	struct barcode_hash_entry *bcentry;
	struct barcode bc;
	char bchash[HASH_BITS+1];
	struct electorate *elecs, *i;
	PGconn *conn;
	int ppcode;
	
	fprintf(stderr,"authenticate: running as %s\n",getlogin());
	fprintf(stderr,"authenticate: Starting authentication\n");

	/* Our own failure function */
	set_cgi_bailout();
	fprintf(stderr,"authenticate: set bailout\n");
	fprintf(stderr,"authenticate: get_database_port() will return %s\n",get_database_port());

	/* Can be called on slave as well as master */
	conn = connect_db_port("evacs", get_database_port());
	if (!conn) bailout("authenticate:Could not open database connection:\n%s\n",PQerrorMessage(conn));

	/* Copy barcode ascii code from POST arguments */
	vars = cgi_get_arguments();
	strncpy(bc.ascii, http_string(vars, "barcode"), sizeof(bc.ascii)-1);
	bc.ascii[sizeof(bc.ascii)-1] = '\0';
	http_free(vars);

	/* Extract data and checksum from ascii */
	if (!bar_decode_ascii(&bc))
		cgi_error_response(ERR_BARCODE_MISREAD);

	/* Hash the barcode to look up in the table */
	gen_hash(bchash, bc.data, sizeof(bc.data));

	bcentry = get_bhash_table(conn, bchash);
	if (!bcentry) {
		PQfinish(conn);
		fprintf(stderr, "Barcode `%s' not found\n", bc.ascii);
		cgi_error_response(ERR_BARCODE_AUTHENTICATION_FAILED);
	}

	/* DDS3.2.4: Check Unused */
	if (bcentry->used) {
		PQfinish(conn);
		fprintf(stderr, "Barcode `%s' already used\n", bc.ascii);
		cgi_error_response(ERR_BARCODE_USED);
	}

	ppcode = SQL_singleton_int(conn,"SELECT polling_place_code "
				   "FROM server_parameter;");
	if (ppcode < 0) {
		PQfinish(conn);
		cgi_error_response(ERR_SERVER_INTERNAL);
	}
	fprintf(stderr,"pooling place code, %i\n",bcentry->ppcode);
	if (ppcode != bcentry->ppcode) {
		PQfinish(conn);
		cgi_error_response(ERR_BARCODE_PP_INCORRECT);
	}

	elecs = get_electorates(conn);
	for (i = elecs; i; i = i->next) {
		if (i->code == bcentry->ecode) {
			/* Found it! */
			vars = create_response(conn, i);
			free_electorates(elecs);
			PQfinish(conn);
			cgi_good_response(vars);
		}
	}

	/* Should never happen */
	free_electorates(elecs);
	PQfinish(conn);
	bailout("Barcode electorate %u not found\n", bcentry->ecode);
}

