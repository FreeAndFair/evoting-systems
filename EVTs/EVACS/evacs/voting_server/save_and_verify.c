/* This file is (C) copyright 2001 Software Improvements, Pty Ltd.
   
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/
#include <stdlib.h>
#include <common/barcode_hash.h>
#include "voting_server.h"
#include "save_and_verify.h"

/* DDS3.2.22: Primary Store */
static enum error primary_store_start(PGconn *conn,
				      const struct preference_set *vote,
				      const struct barcode *bc,
				      const struct electorate *elec)
{
	char hash[HASH_BITS + 1];
	int pp_code;
	unsigned int num_rows;
	char *preference_list, *timestamp;
	char *batch_number_string;

	fprintf(stderr,"s&v:PstoreStart: generating hash\n");
	gen_hash(hash, bc->data, sizeof(bc->data));
	/* Get polling_place_code */
	fprintf(stderr,"s&v:PstoreStart: getting ppcode\n");
	pp_code = (unsigned int)SQL_singleton_int(conn,
						  "SELECT polling_place_code "
						  "FROM server_parameter;");
	if (pp_code < 0)
		bailout("Primary store failed. Polling Place code not "
			"found in server_parameter table.");
	fprintf(stderr,"s&v:PstoreStart: ppcode: %u\n",pp_code);

	/* begin transaction */
	begin(conn);


	fprintf(stderr,"s&v:PstoreStart: updating barcode\n");
		
	/* Mark barcode as used */
	num_rows = SQL_command(conn,
			       "UPDATE barcode "
			       "SET used = true "
			       "WHERE hash = '%s' "
			       "AND used = false;",hash);

	/* Check barcode exists and has not been used */
	if (num_rows != 1 )
		return(ERR_COMMIT_FAILED);
	
	fprintf(stderr,"s&v:PstoreStart: generating pref_string&timestamp\n");

	/* accumulate the preferences for the vote */
	preference_list=  preference_string((struct preference_set *) vote);
	timestamp=generate_sortable_timestamp();

	fprintf(stderr,"s&v:PstoreStart: inserting vote\n");

	/* convention for electronic batches is EPPP000*/
	batch_number_string=sprintf_malloc("%u%03u000",elec->code,pp_code);

	/* Store the vote */
	num_rows = SQL_command(conn,
			       "INSERT INTO %s_confirmed_vote"
			       "(batch_number, paper_version, time_stamp, preference_list) "
			       "VALUES(%u,%u,'%s','%s');",
			       elec->name,
			       atoi(batch_number_string),
			       vote->paper_version, 
			       timestamp,
			       preference_list);
	free(batch_number_string);

	fprintf(stderr,"s&v:PstoreStart: freeing mem\n");
	free(preference_list);
	free(timestamp);
	
	fprintf(stderr,"s&v:PstoreStart: returning %u\n",(num_rows==1)?ERR_OK:ERR_COMMIT_FAILED);

	/* Error if not EXACTLY one row updated */
	return ((num_rows==1)?ERR_OK:ERR_COMMIT_FAILED);
}

static enum error primary_store_commit(PGconn *conn)
{
	commit(conn);
	return ERR_OK;
}

static void primary_store_abort(PGconn *conn)
{
	rollback(conn);
}

/* DDS3.2.22: Secondary Store */
static enum error secondary_store(const struct http_vars *vars)
{
	struct http_vars *retvars;
	enum error ret;

	if (!am_i_master())
		/* I am the slave, so this is the secondary store */
		return ERR_OK;

	/* Send to slave for secondary store */
	retvars = http_exchange(SLAVE_SERVER_ADDRESS, SLAVE_SERVER_PORT,
				"/cgi-bin/commit_vote", vars);
	if (!retvars)
		ret = ERR_SERVER_UNREACHABLE;
	else {
		ret = http_error(retvars);
		http_free(retvars);
	}

	return ret;
}

/* DDS3.2.22: Save And Verify Vote */
enum error save_and_verify(PGconn *conn,
			   const struct preference_set *vote,
			   const struct barcode *bc,
			   const struct electorate *elec,
			   const struct http_vars *vars)
{
	enum error err;

	fprintf(stderr,"starting primary store\n");
	err = primary_store_start(conn, vote, bc, elec);
	if (err != ERR_OK) return err;

	fprintf(stderr,"starting secondary store\n");
	err = secondary_store(vars);
	if (err != ERR_OK)
		primary_store_abort(conn);
	else
		err = primary_store_commit(conn);
	return err;
}
