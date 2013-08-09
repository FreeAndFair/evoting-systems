 /* This file is (C) copyright 2000-2004 Software Improvements, Pty Ltd */

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

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h> 
#include <stdlib.h>
#include <common/ballot_contents.h>
#include <common/get_electorate_ballot_contents.h>
#include <common/voter_electorate.h>
#include <common/current_paper_index.h>
#include <common/rotation.h>
#include <common/database.h>
#include <voting_client/image.h>
#include <voting_client/message.h>
#include <voting_client/initiate_session.h>
#include <voting_client/get_rotation.h>
#include <voting_client/vote_in_progress.h>
#include <data_correction/batch_edit.h>
#include <data_correction/batch_edit_2.h>
#include <election_night/update_ens_summaries.h>

#include "enter_paper.h"
#include "confirm_paper.h"
#include "get_paper_version.h"
#include "accumulate_deo_preferences.h"
#include "handle_end_batch_screen.h"

#include "batch_entry.h"

/* global indexing the current papers' Robson Rotation */
static unsigned int current_paper_version;


/* DDS3.4: DEO Set Batch Number 
   from v2B         */
static struct predefined_batch *set_batch_number(void)
{
        unsigned int batch_number;
        struct predefined_batch *batch_source;
	struct electorate *batch_electorate=NULL;
	unsigned int electorate_code=-1;
	struct ballot_contents *bc;
	bool batch_ok=false;
	char electorate_name[100];  /* temporary variable  */
	PGconn *conn;

	conn = connect_db_host(DATABASE_NAME,SERVER_ADDRESS);	
	if (conn == NULL) bailout ("Can't connect to database: %s at %s\n",
				   DATABASE_NAME,SERVER_ADDRESS);
	
	/* loop until a valid batch number (in database) is entered */
	while (batch_ok == false) {
	       printf("Please type a valid batch number to enter: ");
	       batch_number = get_integer();
	       batch_source = resolve_batch_source(conn, batch_number);
	       if (batch_source == NULL) {
		       printf ("No record of batch: %u\n", batch_number);
	       } else {
		       electorate_code = batch_source->electorate_code;
		       batch_ok=true;
	       }
	}
	assert(electorate_code >= 0);
	strcpy(&electorate_name[0],
	       (char *)resolve_electorate_name(conn, electorate_code));
	batch_electorate = malloc(sizeof(*batch_electorate) + 
				  sizeof(char) * (strlen(electorate_name) + 1));
				  
	batch_electorate->code = electorate_code;
	strcpy(batch_electorate->name,electorate_name);
	batch_electorate->num_seats = SQL_singleton_int(conn,
							"SELECT seat_count "
							"FROM electorate "
							"WHERE code = %u;",
							electorate_code);
	store_electorate(batch_electorate);
	free(batch_electorate);
	set_current_batch_number(batch_number);
	
	bc = get_electorate_ballot_contents(conn, electorate_code);
	set_ballot_contents(bc);
	PQfinish(conn);
	return batch_source;
}

/* DDSv2B: Abort Batch Entry */
static bool abort_batch_entry(struct batch_with_error *batch_with_error) 
{
	bool batch_ok = false;
	unsigned int i, num_papers, error;
	
	/* check for an electronic batch (definition: evenly divisible by 1000)*/
	if ( batch_with_error->b.batch_number % 1000 == 0)
		return false;
	
	num_papers = batch_with_error->b.num_papers;
	if (num_papers > 0) {
	       for(i=0; i<num_papers; i++) {
	               error = batch_with_error->papers[i].error_code;
		       if (error == ENTRY_ERR_UNENTERED ||
			   error == ENTRY_ERR_KEYSTROKE) {
			 batch_ok = true;
			 break;
		       }
	       }
        } else {
	  /* first entry for this batch */
	        batch_ok = true;
	}
	return batch_ok;
}

static bool same_deo(PGconn *conn,unsigned int batch_number)
{
	struct batch *batch = get_entered_batch(conn, batch_number);
	struct entry *entry;
	char *operator_id;
	unsigned int i,j;

	operator_id = get_operator_id();

	bool already_entered_by_this_deo = false;
	
	if (batch->b.num_papers != 0) {
		for (i=0; i < batch->b.num_papers; i++) {
		  j=0;
			for (entry=batch->papers[i].entries; entry; entry=entry->next) {
			  j++;
				if (strcmp(entry->e.operator_id, operator_id) == 0) {
					already_entered_by_this_deo = true;
					break;
				}
			}
			if (already_entered_by_this_deo) break;
		}
	}
	free_batch(batch);
	free(operator_id);
	return (already_entered_by_this_deo);
}

/* DDS3.4: Start Next Batch Entry 
   from v2B         */
static struct predefined_batch *start_next_batch_entry(void)
{
        bool batch_ok=false;
	PGconn *conn;
        struct predefined_batch *batch_info;
	struct batch_with_error *batch_with_error;
	struct batch *batch;
	const char *operator_id = get_operator_id();
	unsigned int batch_size;

	conn = connect_db_host(DATABASE_NAME,SERVER_ADDRESS);
	if (conn == NULL) bailout("Can't connect to %s at %s\n",
				  DATABASE_NAME,SERVER_ADDRESS);
/* dont allow a deo to enter a batch which he/she has already entered */

/* dont allow a deo to enter a correct batch, or a batch with an error which 
   is not a KEYSTROKE error */
/* don't allow a deo to enter an electronic batch (batch #'s ****000) */
	while (batch_ok == false) {
		batch_info=NULL;
	        while (batch_info == NULL) {
			batch_info = malloc(sizeof(*batch_info));
		        batch_info = set_batch_number();
			
			if (same_deo(conn,batch_info->batch_number)) {
				printf("You (%s) have already entered that batch"
				       ". Please choose another.\n",operator_id);
				batch_info = NULL;
			}
		}
		batch = get_entered_batch(conn, batch_info->batch_number);
		batch_with_error = find_errors_in_batch(conn,batch,
					(char *)get_voter_electorate()->name);
		batch_ok = abort_batch_entry(batch_with_error);
		if (!batch_ok) {
			printf ("That batch is either correct or "
				       "contains errors which need "
				       "supervisor approval.\n");
		} else {
			batch_size=batch->b.batch_size;
			if (! batch_size) chng_batch_size(conn, 
							  batch_info->batch_number);
		} 
	}
	PQfinish(conn);
	free_batch_with_error(batch_with_error);
	return batch_info;
}

static void set_current_paper_version(unsigned int paper_version)
{
	current_paper_version = paper_version;
}

/* DDSv2B 3.7: Start New Paper */
static bool start_new_paper(void) 
{
        int paper_version;
	bool end_batch = false;
	struct rotation *rot;

	fprintf(stderr, "\nEntered start_new_paper\n");
	paper_version = get_paper_version();
	
	/* paper_version number -1 is reserved for signalling end of batch */
	if (paper_version == -1) {
		end_batch = true; 
		fprintf(stderr, "Leaving start_new_paper/2\n");
		return end_batch;
	}
	
	set_current_paper_version(paper_version);
	rot = get_rotation_from_pvn(get_voter_electorate(),paper_version);
	set_current_rotation(rot);
	free(rot);
	
	/* Clear the vote in progress */
	delete_prefs();

	fprintf(stderr, "Leaving start_new_paper\n");
	return end_batch;
}

static unsigned int get_current_paper_version(void)
{
	return current_paper_version;
}


/* DDS3.2: Batch Entry 
   from v2B         */
void batch_entry(void) {

	bool end_batch, confirm_end_batch;
	bool cancelled;
	PGconn *conn;
	unsigned int entries=0;
	struct predefined_batch *batch_info;
	char *electorate_name;
	int paper_version=-1;

	open_log_file("batch_entry");
	fprintf(stderr, "\nEntered batch_entry\n");

	while (1) {
		batch_info = NULL;
		end_batch=false;
		confirm_end_batch=false;
		while (batch_info == NULL) {
			batch_info = start_next_batch_entry();
		}
		
		electorate_name=(char *)get_voter_electorate()->name;
		/* loop until handle_end_batch returns confirm_end_batch=true */
		while (confirm_end_batch == false) {

			while (end_batch == false) {
				end_batch = start_new_paper();
				
				if (end_batch == false){
					cancelled = enter_paper();
					
					if (cancelled == false) { 
						paper_version=
						     get_current_paper_version();
						assert(paper_version > 0);
						confirm_paper(paper_version);
						
					}
				}
			}
			confirm_end_batch = handle_end_batch_screen();
			end_batch = confirm_end_batch;
		}

		conn = connect_db_host(DATABASE_NAME,SERVER_ADDRESS);
		if (!conn) bailout("Can't connect to %s at %s\n",
				   DATABASE_NAME,SERVER_ADDRESS);

		entries = (unsigned int)
			SQL_singleton_int(conn,
					  "SELECT MAX(e.index) "
					  "FROM %s_entry e,%s_paper p "
					  "WHERE p.batch_number = %u "
					  "AND e.paper_id = p.id; ",
					  electorate_name,electorate_name,
					  batch_info->batch_number);

		/* log entry to batch history */
		log_batch_operation(conn, batch_info->batch_number,
				    (enum batch_op) ENTRY, 
				    entries,
				    get_current_paper_index()-1
				    );
		fprintf(stderr, "Batch %u entry %u complete\n",
			batch_info->batch_number,entries);
		clear_current_paper_index();
		PQfinish(conn);
		fflush(stderr);

	}
	close_log_file();

}





