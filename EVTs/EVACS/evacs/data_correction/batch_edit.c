/* This file is (C) copyright 2001-2008 Software Improvements, Pty Ltd */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public license for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */
#include <stdlib.h>
#include <ctype.h>
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include <time.h>
#include <common/database.h>
#include <election_night/update_ens_summaries.h>
#include <common/batch.h>
#include <common/find_errors.h>
#include <common/current_paper_index.h>
#include <common/rotation.h>
#include <common/voter_electorate.h>
#include <common/get_electorate_ballot_contents.h>
#include <voting_client/vote_in_progress.h>
#include <voting_client/get_rotation.h>
#include <data_entry/get_paper_version.h>
#include <data_entry/confirm_paper.h>
#include <data_entry/enter_paper.h>
#include <data_entry/batch_entry.h>
#include <voting_server/fetch_rotation.h>

#include "batch_edit.h"
#include "batch_edit_2.h"

static bool printer=true;

/* SIPL 2011: Commented out the following function because it is never used. */
/* return the maximum of two values */
/* static int max(unsigned int value1, unsigned int value2) { */
/* 	if (value1 >= value2)  */
/* 		return value1; */
/* 	else  */
/* 		return value2; */
/* } */

/* output a header containing user and timestamp for the report */
void print_report_heading(FILE *fp) {
   char *operator_id=get_operator_id();
   char *timestamp = generate_timestamp();
   fprintf(fp,"------------------------------------------------------------------------------\n");
   fprintf(fp,"USER: %s\t\t\t\t\t%s\n",operator_id, timestamp );
   fprintf(fp,"------------------------------------------------------------------------------\n");
   
   free(timestamp);
   free(operator_id);
}

void wait_for_reset(void)
{
	bailout("Failed to receive image from server. Is server down?\n");
}

void printfile(const char *filename)
/*
  Send the file to the printer via a system command.
*/
{
	char *command;
	if (printer == false)
		/* echo to screen */
		command = sprintf_malloc("echo;cat %s",filename);
	else
		/* send to printer via lpr command */
		command = sprintf_malloc("lpr %s\n",filename);
  	system(command); 
	free(command);
}
/* count the number of entries in paper */
static unsigned int num_entries(struct paper_with_error *p)
{
	unsigned int i=0;
	struct entry_with_error *e;

	for (e=p->entries;e;e=e->next) i++;

	return i;
}

/* DDS3.36: Print Paper */
static void print_paper(PGconn *conn,
			struct paper_with_error *p,
			unsigned int e_code,
			unsigned int batch_number,
			FILE *fp,
			bool active_entries_only)
/*
  Print the entries for a paper.
*/
{
	PGresult *result;
	struct entry_with_error *e, *a1={ NULL }, *a2={ NULL };
	char *candidate_name, *candidate_name1, *candidate_name2;
	unsigned int i,pref_limit=0;
	unsigned int temp = 0;
	int entry_id1=0, entry_id2=0, paper_id;
	unsigned int entry_index=num_entries(p);
	const char *electorate_name=resolve_electorate_name(conn,e_code);
	char *active_flag;
	const char *tab         = (char *) "\t";
	const char *dbltab      = (char *) "\t\t";	
	const char *empty       = (char *) " \0";
	const char *flag        = (char *) "*\0";
	char *print_flag= (char *) empty;
	char *pref_flag= (char *) empty;
	char *prefnum1, *prefnum2;
	char *candidate_separator;
	bool compare=true;
	
	fprintf(stderr, "\nEntered print_paper (PP)\n");
	fprintf(stderr, "    e_code ..... %u\n", e_code);
	fprintf(stderr, "    batch_number %u\n", batch_number);
	fprintf(stderr, "PP: electorate_name is '%s'\n", electorate_name);

	/* retrieve active entries */
	fprintf(stderr,
		"\nPP: Issue sql query: SELECT id FROM %s_paper "
		"WHERE batch_number = %u AND index = %u;\n",
		electorate_name,
		batch_number, p->p.index);

	paper_id = SQL_singleton_int(conn,
				     "SELECT id "
				     "FROM %s_paper "
				     "WHERE batch_number = %u "
				     "AND index = %u;",
				     electorate_name, 
				     batch_number,p->p.index);

	fprintf(stderr, "PP: paper_id is %u\n", paper_id);

	fprintf(stderr,
		"\nPP: Issue sql query: "
		"SELECT entry_id1, entry_id2 "
		"FROM %s_paper WHERE id = %u;\n",
		electorate_name,
		paper_id);

	result = SQL_query(conn,
			   "SELECT entry_id1, entry_id2 "
			   "FROM %s_paper WHERE id = %u;",
			   electorate_name, paper_id
		);
	
	if (PQntuples(result) > 0 ) { 
		entry_id1 = atoi(PQgetvalue(result,0,0));
		entry_id2 = atoi(PQgetvalue(result,0,1));
	} 
	
	PQclear(result);

	/* iterate through every entry of this paper */

	fprintf(stderr, "PP: entry_index is %u\n", entry_index);
	fprintf(stderr, "PP: entry_id1   is %d\n", entry_id1);
	fprintf(stderr, "PP: entry_id2   is %d\n", entry_id2);

	for (e=p->entries;e;e=e->next,entry_index--) {
	  fprintf(stderr, "PP: p->entries->e.index is %u\n", e->e.index);

		active_flag= (char *) empty;
		compare=true;
		
		/* collect the 2 active entries */
		if (e->e.index==entry_id1) {
			a1=e;
		        active_flag= (char *) flag;
		}
		else if (e->e.index==entry_id2) {
			a2=e;
		        active_flag=(char *) flag;
		}
		
		if (active_entries_only) 
			/* just collect the active entries if filter flag set*/
			continue;
		
		/* Print heading for 'in-line' report (all entries) */
		fprintf(stderr, "PP: %d\t%d%s\t%s\t%s\t%u\n",
			p->p.index,
			e->e.index,
			active_flag,
			e->e.operator_id,
			get_error_string(e->error_code),
			e->e.paper_version_num);

		fprintf(fp,"%d\t%d%s\t%s\t%s\t%u\n",
			p->p.index,
			e->e.index,
			active_flag,
			e->e.operator_id,
			get_error_string(e->error_code),
			e->e.paper_version_num);

		/* iterate through the preferences for this entry */
		for (i=0;i < e->e.num_preferences;i++) {
		  fprintf(stderr, "PP: preference index is %u\n", i);
			/* DDS3.36: Get Candidate Name */
		  fprintf(stderr,
			  "\nPP: Issue sql query: "
			  "SELECT name FROM candidate\n"
			  "      WHERE index = %u AND party_index = %u "
			  "AND electorate_code = %u;\n",
			  e->preferences[i].db_candidate_index,
			  e->preferences[i].group_index,
			  e_code);
			candidate_name = 
				SQL_singleton(conn,
					      "SELECT name "
					      "FROM candidate "
					      "WHERE index = %u "
					      "AND party_index = %u "
					      "AND electorate_code = %u;",
					      e->preferences[i].db_candidate_index,
					      e->preferences[i].group_index,
					      e_code);
			assert(candidate_name);
			/* print his preference */
			fprintf(stderr, "PP: \t\t\t\t\t%u\t%s\n",
				e->preferences[i].prefnum,
				candidate_name);
			fprintf(fp,"\t\t\t\t\t%u\t%s\n",
				e->preferences[i].prefnum,
				candidate_name);
			free(candidate_name);
		}
	}
	
	
	if (active_entries_only) {
		pref_limit = 0;
		temp = 0;
		if (!a2) 
			/* No corresponding  entry to compare a1 against */
			compare=false;
		if (!a1) {
			compare = false;
		}
		/* assign 'match flag' for paper version */
		if (compare && 
		    a1->e.paper_version_num == a2->e.paper_version_num ) 
			print_flag = (char *)empty;
	        else 
			print_flag = (char *)flag;
		
                if (!a1 && a2)
                  fprintf(fp, "\t\t\t\t");

                if (a1)
                  fprintf(fp,"%d\t%d\t%s\t%s\t%s%u",
			/* Paper index common to both entries */
			p->p.index,
			
			/* Active entry one */
			a1->e.index,
			a1->e.operator_id,
			get_error_string(a1->error_code),
			print_flag,
			a1->e.paper_version_num
			);
		
                /* Active entry two (if exists)*/		
		if (a2) {
			fprintf(fp,"\t%d\t%s\t%s\t%s%u\n",
				a2->e.index,
				a2->e.operator_id,
				get_error_string(a2->error_code),
				print_flag,
				a2->e.paper_version_num
				);
		} else {
			fprintf(fp,"\n");
		}

                if (a1) pref_limit = a1->e.num_preferences;
                if (a2) temp       = a2->e.num_preferences;
                if (temp > pref_limit) pref_limit = temp;

			/* run through and display preferences */
		for (i=0;
		     i < pref_limit;
		     i++) {
		  fprintf(stderr, "PP: Run through and display preferences, index is %u\n", i);
		  if (!a1 && !a2) fprintf(stderr, "PP: ERROR: a1 and a2 are NULL\n");
			/* DDS3.36: Get Candidate Name */
			if ((a1) && (i < a1->e.num_preferences))
				candidate_name1 = 
					SQL_singleton(
						conn,
						"SELECT name "
						"FROM candidate "
						"WHERE index = %u "
						"AND party_index = %u "
						"AND electorate_code = %u;",
						a1->preferences[i].db_candidate_index,
						a1->preferences[i].group_index,
						e_code);
			else candidate_name1 = NULL;
			
			if ((a2) && (i < a2->e.num_preferences))
				candidate_name2 = 
					SQL_singleton(
						conn,
						"SELECT name "
						"FROM candidate "
						"WHERE index = %u "
						"AND party_index = %u "
						"AND electorate_code = %u;",
						a2->preferences[i].db_candidate_index,
						a2->preferences[i].group_index,
						e_code);
			else candidate_name2 = NULL;
			
			fprintf(stderr, "PP: candidate 1 is '%s'\n",
				candidate_name1);
			fprintf(stderr, "PP: candidate 2 is '%s'\n",
				candidate_name2);

			/* number of TABs required to align preferences */
			if (candidate_name1) {
				if (strlen(candidate_name1)<9)
					candidate_separator = (char *) dbltab;
				else
					if (strlen(candidate_name1)>16)
						candidate_separator = (char *) empty;
					else 
						candidate_separator = (char *) tab;
			} else {
				candidate_separator = (char *) dbltab;
			}

			/* do the names match? */
			if (candidate_name1 &&
			    candidate_name2 &&
			    strcmp(candidate_name1,candidate_name2) != 0) 
				print_flag = (char *)flag;
			else 
				print_flag = (char *)empty;
			
			/* assign formatted strings for pref numbers */
			if (candidate_name1)
				prefnum1 = 
				    sprintf_malloc("%02u",
						   a1->preferences[i].prefnum);
			else 
				prefnum1 = sprintf_malloc("--");

			if (candidate_name2)
				prefnum2 = 
				    sprintf_malloc("%02u",
						   a2->preferences[i].prefnum);
			else 
				prefnum2 = sprintf_malloc("--");
			
			/* do the preference numbers match? */
			if ( strcmp(prefnum1,prefnum2) == 0) 
				/* yes - set flag to empty */
				pref_flag = (char *)empty;
			else 
				/* no - set flag to asterisk */
				pref_flag = (char *)flag;
			
			/* print left hand entry */		
			fprintf(fp,"Preference %s%s%s%s",
				pref_flag,
				prefnum1,
 
				print_flag,
				candidate_name1
				
			);
			if (a2) 
				/* print right hand entry */ 
				fprintf(fp,"%s\t%s%s%s%s\n",
					candidate_separator,
					pref_flag,
					prefnum2,
					
					print_flag,
					candidate_name2	);
			else 
				fprintf(fp,"\n");
			
			free(prefnum1);
			free(prefnum2);
			if (candidate_name1) free(candidate_name1);
			if (candidate_name2) free(candidate_name2);
		}	
	}
	
	if (p->p.supervisor_tick) 
		fprintf(fp,"PAPER APPROVED\n");

	fprintf(fp,"\n");

   fprintf(stderr, "PP: Leaving print_paper\n");
}

/* DDS3.8: Prompt for Batch Number */
static void batch_num_prompt(void)
/*
  Print a text prompt.
*/
{
	printf("Please enter batch number: ");
}

/* DDS3.8: Get Batch Number from User */
static unsigned int get_batch_num(void)
/*
  Obtain a batch number from the user.
*/
{
	char *line;
	unsigned int b_num;

	batch_num_prompt();
	line = fgets_malloc(stdin);
	b_num = (unsigned int)atoi(line);
	free(line);
	return(b_num);
}

/* DDS3.8: Set Uncommitted Batch Number */
static bool set_uncom_batch_num(PGconn *conn,unsigned int *batch_number,
				unsigned int electorate_code)
/*
  Input a Batch Number and Batch Number OK = TRUE if it is valid
  and uncommitted.
*/
{
	unsigned int b_num,e_code=0,num_rows;
	PGresult *result;
	bool committed=false;

	b_num = get_batch_num();

	result = SQL_query(conn,
			   "SELECT electorate_code,committed "
			   "FROM batch "
			   "WHERE number = %u;",b_num);

	if ((num_rows = PQntuples(result)) > 0) {
		/* DDS3.8: Get Electorate Code from Predefined Batch Details */
		e_code = (unsigned int)atoi(PQgetvalue(result,0,0));
		committed = (*PQgetvalue(result,0,1) == 't') ? true : false;
	}

	PQclear(result);

	if (num_rows < 1) {
		printf("Unknown batch number.\n");
		return(false);
	}
	
	/* DDS3.8: Get Electorate Code from Batch Electorate */
	if (electorate_code != e_code) {
		printf("That batch number is not in this electorate.\n");
		return(false);
	} 

	/* check for an electronic batch (definition: evenly divisible by 1000)*/
	if ( b_num % 1000 == 0) {
		printf("That is an electronic batch and cannot be modified.\n");  
		return false;
	}	
	
	if (committed) {
		printf("This batch has already been committed.\n");
		return(false);
	}

	*batch_number = b_num;
	return(true);
}

/* DDS3.32: Set Batch Number */
static bool set_batch_num(PGconn *conn,unsigned int *batch_number,
			  unsigned int electorate_code)
/*
  Input a Batch Number. Return true and the batch number if the number is a
  valid batch number. Otherwise return false.
*/
{
	unsigned int b_num,e_code=0,num_rows;
	PGresult *result;

	b_num = get_batch_num();

	result = SQL_query(conn,
			   "SELECT electorate_code "
			   "FROM batch "
			   "WHERE number = %u;",b_num);

	if ((num_rows = PQntuples(result)) > 0)
		/* DDS3.8: Get Electorate Code from Predefined Batch Details */
		e_code = (unsigned int)atoi(PQgetvalue(result,0,0));

	PQclear(result);

	if (num_rows < 1) {
		printf("Unknown batch number.\n");
		return(false);
	}
	
	/* DDS3.8: Get Electorate Code from Batch Electorate */
	if (electorate_code != e_code) {
		printf("That batch number is not in this electorate.\n");
		return(false);
	}

	*batch_number = b_num;
	return(true);
}

/* DDS3.40: Print Errors in Batch */
void print_errors_in_batch(PGconn *conn,unsigned int batch_number)
/*
  Print all Papers in a Batch which are either informal or have Keystroke
  Errors.
*/
{
	bool committed_flag,print;
	const char *committed_text;
	char *electorate_name;
	char *polling_place_name;
	struct batch *batch;
	struct batch_with_error *bwe;
	unsigned int i,e_code;
	FILE *fp;
	char tmpfile[]="/tmp/errors_in_batch_XXXXXX";

	fprintf(stderr, "\nEntered print_errors_in_batch (PEiB)\n");
	fprintf(stderr, "   batch_number: %u\n", batch_number);

	fprintf(stderr,
		"\nPEiB: Issue sql query: SELECT p.name FROM "
		"batch b, polling_place p\n"
		"WHERE b.number = %u AND p.code = b.polling_place_code;\n",
		batch_number);

	polling_place_name = SQL_singleton(conn,
				  "SELECT p.name "
				  "FROM batch b, polling_place p "
				  "WHERE b.number = %u "
				  "AND p.code = b.polling_place_code;",
					   batch_number);

	fprintf(stderr, "PEiB: polling_place_name is '%s'\n",
		polling_place_name);

	fprintf(stderr,
		"\nPEiB: Issue sql query: SELECT committed "
		"FROM batch WHERE number = %u;\n",
		batch_number);

	committed_flag = SQL_singleton_bool(conn,
					    "SELECT committed "
					    "FROM batch "
					    "WHERE number = %u;",batch_number);

	if (committed_flag) fprintf(stderr, "PEiB: committed is true\n");
	else                fprintf(stderr, "PEiB: committed is false\n");

	fprintf(stderr,
		"\nPEiB: Issue sql query: SELECT electorate_code "
		"FROM batch WHERE number = %u;\n",
		batch_number);

	e_code = SQL_singleton_int(conn,
				   "SELECT electorate_code "
				   "FROM batch "
				   "WHERE number = %u;",batch_number);
	fprintf(stderr, "PEiB: e_code is %d\n", e_code);

	fprintf(stderr,
		"\nPEiB: Issue sql query: SELECT name FROM electorate "
		"WHERE code = %u;\n",
		e_code);

	electorate_name = SQL_singleton(conn,
					"SELECT name "
					"FROM electorate "
					"WHERE code = %u;",e_code);

	fprintf(stderr, "PEiB: electorate_name is '%s'\n", electorate_name);

	committed_text = (committed_flag)?"COMMITTED":"";

	mkstemp(tmpfile);
	fp = fopen(tmpfile,"w");
	
	print_report_heading(fp);
	fprintf(fp,"Papers with Errors for %s from %s Batch: %u %s\n"
		"Paper\tEntry \n"
		"Index\tIndex\tUser\tError\tPVN\tPreferences\n"
		"----------------------------------------"
		"----------------------------------------\n",
		electorate_name,polling_place_name,batch_number,committed_text);
		
	fprintf(stderr,
		"PEiB: CALL: get_entered_batch(conn, batch_number=%u)\n",
		batch_number);

	batch = get_entered_batch(conn,batch_number);
	fprintf(stderr,
		"PEiB: CALL: find_errors_in_batch"
		"(conn, batch, electorate_name='%s'\n",
		electorate_name);
	bwe = find_errors_in_batch(conn, batch, electorate_name);

	free(electorate_name);
	free(polling_place_name);

	for (i=0;i<bwe->b.num_papers;i++) {
	  fprintf(stderr,
		  "** paper index %u - error_code is '%s' - %u\n",
		  i+1,
		  get_error_string(bwe->papers[i].error_code),
              bwe->papers[i].error_code);
		print = true;
		switch (bwe->papers[i].error_code) {
		case ENTRY_ERR_CORRECT:
		case ENTRY_ERR_CORRECTED:
			print = false;
			break;
		case ENTRY_ERR_IGNORED:
		case ENTRY_ERR_INFORMAL:
		case ENTRY_ERR_MISSING_NUM:
		case ENTRY_ERR_DUPLICATED_NUM:
			if (bwe->papers[i].p.supervisor_tick)
				print = false;
			break;
		case ENTRY_ERR_UNENTERED:
		case ENTRY_ERR_KEYSTROKE:
			break;

		case ENTRY_ERR_INVALID_BATCH_APPROVAL:
			break;
		}
		
		if (print) {
		  fprintf(stderr, "PEiB: print papers[%u]\n", i);
			print_paper(conn,
				    &bwe->papers[i],
				    e_code,bwe->b.batch_number,fp,true);
		}
	}
	free_batch_with_error(bwe);
	fclose(fp);
	printfile(tmpfile);
	printf("Errors in Batch %u printed.\n",batch->b.batch_number);
	free_batch(batch);
}

/* DDS3.38: Set Polling Place */
static bool set_polling_place(PGconn *conn,unsigned int *polling_place_code)
/*
  Allow operator to choose a polling place for reporting.
  Return true and the polling place code if polling place is valid.
  Otherwise return false.
*/
{
	int pp_code;
	char *pp_name;

	printf("Please enter the polling place name>");
	pp_name = fgets_malloc(stdin);

	/* DDS3.38: Resolve Polling Place Code */
	/* DDS3.38: Store Current Polling Place */
	pp_code = SQL_singleton_int(conn,
				    "SELECT code "
				    "FROM polling_place "
				    "WHERE UPPER(name) = UPPER('%s');"
				    ,pp_name);
	free(pp_name);
	if (pp_code == -1 ) {
		printf("Polling place %s unknown\n\n",pp_name);
		return(false);
	}
	
	*polling_place_code = pp_code;
	return(true);
}

/* DDS3.38: Print Batches for Polling Place */
void print_pp_batches(PGconn *conn, 
		      unsigned int electorate_code,
		      unsigned int polling_place_code)
/*
  Output to printer a report detailing batches originating from a polling place
*/
{
	unsigned int num_rows,i,j;
	int num_papers;
	char *pp_name, *elec_name;
	const char *committed;
	PGresult *result;
	struct batch *batch;
	struct batch_with_error *bwe;
	char tmpfile[]="/tmp/print_pp_batches_XXXXXX";
	FILE *fp;
	bool next_batch;

	pp_name = SQL_singleton(conn,
				"SELECT name "
				"FROM polling_place "
				"WHERE code = %u;",polling_place_code);
	
	elec_name = (char *)get_voter_electorate()->name;
	mkstemp(tmpfile);
	fp = fopen(tmpfile,"w");

	print_report_heading(fp);
	fprintf(fp,"Batch report for Polling Place: %s (electorate %s)\n\n",
		pp_name, elec_name);

	result = SQL_query(conn,
			   "SELECT number,electorate_code,size,committed "
			   "FROM batch "
			   "WHERE polling_place_code = %u "
			   " AND electorate_code = %u "
			   "ORDER BY number;",
			   polling_place_code,
			   electorate_code);

	num_rows = PQntuples(result);

	for (i=0;i<num_rows;i++) {
		batch = get_entered_batch(conn,atoi(PQgetvalue(result,i,0)));
		bwe = find_errors_in_batch(conn,batch,elec_name);
		committed = (*PQgetvalue(result,i,3)=='t')?"COMMITTED":"";
		fprintf(fp,"Batch:%u size:%u\t%s\t\n",
			batch->b.batch_number,
			batch->b.batch_size, 
			committed);

		/* set up loop */
		j = 1;
		do {
			num_papers = 
				SQL_singleton_int(conn,
						  "SELECT COUNT(e.id) "
						  "FROM %s_entry e, %s_paper p "
						  "WHERE e.index = %u "
						  "AND e.paper_id = p.id "
						  "AND p.batch_number = %u;",
						  elec_name, elec_name,
						  j,batch->b.batch_number);
			if (num_papers > 0)
				fprintf(fp,"\tNumber of papers with "
					"entry index %u = %d\n",
					j,num_papers);
			j++;
		
		} while (num_papers >  0);
		
		next_batch = false;

		if (bwe->b.batch_size != bwe->b.num_papers) {
			fprintf(fp,"INCOMPLETE ENTRY\n");
			next_batch=true;
		}	
		if (next_batch == true) continue;

		for (j=0;j<bwe->b.num_papers;j++) {
		        if  (bwe->papers[j].error_code == ENTRY_ERR_KEYSTROKE) {
			        fprintf(fp,"ENTRY ERROR\n");
				next_batch=true;
				break;
			}
		}
		/* move on to next batch */
		if (next_batch == true) continue;
     
		/* look for papers needing approval */
		for (j=0;j < bwe->b.num_papers;j++) {
		        /* Increment appropriate counter */
		        if  (bwe->papers[j].error_code == ENTRY_ERR_IGNORED ||
			     bwe->papers[j].error_code == ENTRY_ERR_INFORMAL ||
			     bwe->papers[j].error_code == ENTRY_ERR_MISSING_NUM ||
			     bwe->papers[j].error_code == ENTRY_ERR_DUPLICATED_NUM) {
			        
			        next_batch = true;
				if (bwe->papers[j].p.supervisor_tick == false) 
					fprintf(fp,"APPROVAL NEEDED\n");
				else 
					fprintf(fp,"APPROVED\n");
				break;
			}
		}
		/* move on to next batch */
		if (next_batch == true) continue;	
		
		for (j=0;j<bwe->b.num_papers;j++) {
		        if  (bwe->papers[j].error_code == ENTRY_ERR_CORRECTED) {
			        fprintf(fp,"CORRECTED \n");
				next_batch=true;
				break;
			}
		}
	        /* move on to next batch */
		if (next_batch == true) continue;	

		if (bwe->b.num_papers == 0) 
		        fprintf(fp,"NOT YET ENTERED\n"); 
		else
			fprintf(fp,"CORRECT\n");

		free_batch(batch);
		free_batch_with_error(bwe);
	}
	PQclear(result);
	fclose(fp);
	printfile(tmpfile);
	printf("Batches for %s printed.",pp_name);
	free(pp_name);
}

/* DDS3.34: Print Batch */
void print_batch(PGconn *conn,
		 unsigned int batch_number, 
		 bool active_entries_only)
/*
  Print the entire detail for the active entries of every paper in the
  batch.
*/
{
	PGresult *result;
	const char *committed;
	struct batch *batch;
	struct batch_with_error *bwe;
	const char *match = (char *)"\0";
	const char *nomatch = (char *) "*";
	char *match_flag;
	unsigned int i;
	char tmpfile[] = "/tmp/print_batch_XXXXXX";
	FILE *fp;

	fprintf(stderr, "\nEntered print_batch\n");
	fprintf(stderr, "    batch_number .. %u\n", batch_number);
	if (active_entries_only)
	  fprintf(stderr, "    print active entries only\n");
	else
	  fprintf(stderr, "    print all entries\n");

	/* DDS3.34: Resolve Polling Place Name */
	/* DDS3.34: Get Polling Place Code */
	/* DDS3.34: Get Polling Place name */
	result = SQL_query(conn,
			   "SELECT e.name,p.name,b.number,"
			          "b.committed,e.code "
			   "FROM batch b, electorate e,polling_place p "
			   "WHERE b.number = %u " 
			   "AND e.code = b.electorate_code "
			   "AND p.code = b.polling_place_code;",batch_number);

	committed = (*PQgetvalue(result,0,3) == 't') ? "COMMITTED" : "";
	batch = get_entered_batch(conn,atoi(PQgetvalue(result,0,2)));

	mkstemp(tmpfile);
	fp = fopen(tmpfile,"w");
	print_report_heading(fp);
	
	if (batch->b.batch_size != batch->b.num_papers)
		match_flag=(char *)nomatch;
	else
		match_flag=(char *)match;
	
	fprintf(fp,
		"Batch Dump of active entries for %s from %s Batch: %s %s\n"
		"Declared Size %s%u\tActual size %s%u\n", 
		PQgetvalue(result,0,0),
		PQgetvalue(result,0,1),
		PQgetvalue(result,0,2),
		committed,
		match_flag,batch->b.batch_size,
		match_flag,batch->b.num_papers);
	
	if (active_entries_only) 
		fprintf(fp,
			"Paper\tEntry\t\t\t\tEntry\n"
			"Index\tIndex\tUser\tError\tPVN"
			"\tIndex\tUser\tError\tPVN\n"
			"---------------------------------------"
			"---------------------------------------\n");
	else
		fprintf(fp,
			"Paper\tEntry\n"
			"Index\tIndex\tUser\tError\tPVN\tPreferences\n"
			"---------------------------------------"
			"---------------------------------------\n");

	
	bwe = find_errors_in_batch(conn,batch,
                                   (char *)get_voter_electorate()->name);

	for (i=0;i<bwe->b.num_papers;i++)
		print_paper(conn,&bwe->papers[i],
			    atoi(PQgetvalue(result,0,4)),
			    bwe->b.batch_number,fp,active_entries_only);

	free_batch_with_error(bwe);
	PQclear(result);
	fclose(fp);
	printfile(tmpfile);
	printf("Batch %u printed.\n",batch->b.batch_number);
	free_batch(batch);
	fprintf(stderr, "Leaving print_batch\n");
}


/* DDS3.30: Print Batch Summary */
void print_batch_summary(PGconn *conn)
/*
  Output to printer an overall Tally of batches (by Polling Place) in
  each possible Batch state.
*/

{
	PGresult *result;
	unsigned int num_rows,i,j, electorate_code,polling_place_code;
	unsigned int new_electorate_code ,new_polling_place_code;
	unsigned int batches=0,committed=0,unentered=0,once_entered=0,
		keystroke=0,unapproved=0,uncommitted=0;
	char *electorate_name,*polling_place_name;
	struct electorate *electorate = 
		(struct electorate *)  get_voter_electorate();
	struct batch *batch;
	struct batch_with_error *bwe;
	char tmpfile[]="/tmp/batch_summary_XXXXXX";
	bool next_batch;
	FILE *fp;
	
	fprintf(stderr, "\nEntered print_batch_summary\n");

	/* DDS3.30: Get Batch Information */
	fprintf(stderr,"Retrieving batch data...");
	fprintf(stderr,
		"\nIssue sql query: SELECT e.name, "
		"e.code, p.name, p.code, b.number, "
		"b.committed, b.size\n"
		"       FROM batch b, electorate e, polling_place p\n"
		"       WHERE b.electorate_code = %u "
		"AND b.polling_place_code = p.code "
		"AND b.electorate_code = e.code\n"
		"       ORDER BY e.name, p.name, b.number;\n",
           electorate->code);
	fflush(stderr);

	result = SQL_query(conn,
			   "SELECT e.name,e.code,p.name,p.code,b.number,"
			   "b.committed, b.size "
			   "FROM batch b, electorate e, polling_place p "
			   "WHERE b.electorate_code=%u "
			   "AND b.polling_place_code = p.code "
			   "AND b.electorate_code = e.code "
			   "ORDER BY e.name,p.name,b.number;",
			   electorate->code);
	
	fprintf(stderr,"Done.\n");
	
	num_rows = PQntuples(result);
	fprintf(stderr, "num_rows is %u\n", num_rows);

	mkstemp(tmpfile);
	fp = fopen(tmpfile,"w");

	print_report_heading(fp);

	electorate_name = polling_place_name = (char *)"";
	electorate_code = polling_place_code=0;
	/* for each batch */
	for (i=0;i<num_rows;i++) {
		new_electorate_code=atoi(PQgetvalue(result,i,1));
		new_polling_place_code=atoi(PQgetvalue(result,i,3));
		/* Electorate name or Polling Place name change? */
		if (electorate_code != new_electorate_code ||
		    polling_place_code != new_polling_place_code) {
			/* print any accumulated counters */
			if ( batches > 0 )
				fprintf(fp,"\t\t%u\t%u\t%u\t%u\t%u\t%u\n",
					committed,unentered,once_entered,
					keystroke,unapproved,uncommitted);
			batches = committed = unentered = once_entered =
				keystroke = unapproved = uncommitted = 0;
			/* Electorate name change */
			if (electorate_code != new_electorate_code) {
				electorate_name = PQgetvalue(result,i,0);
				electorate_code=new_electorate_code;
				fprintf(fp,"\nBatch summary for %s:\n"
					"--------------------------------\n"
					"Polling Place\t\t\tSummary\n"
					"--------------------------------"
					"--------------------------------\n",
					electorate_name);
				fprintf(fp,"\t\tcommtd\tunentrd\t"
					"once\tkstroke\t"
					"unapprd\tuncommtd\n");
				fprintf(fp,"\t\t------\t-------\t"
					"----\t-------\t"
					"-------\t--------\n");
				/* ready  new polling place in new electorate */
				polling_place_code = 0;
			}
			
			/* Polling Place name change */
			if (polling_place_code != new_polling_place_code){
				polling_place_name = PQgetvalue(result,i,2);
				polling_place_code=new_polling_place_code;
				/* Print new Polling place heading  */
				fprintf(fp,"%s\n", polling_place_name);
				fprintf(stderr,
					"\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
					"\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
					"\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
					"\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b"
					"%s   %s"
					"                      ",
				 	electorate_name, polling_place_name);
				fflush(stderr);
				
			}
		}
		
		batches++;
		
		if (*PQgetvalue(result,i,5) == 't') { /* committed? */
			committed++;
			continue;
		}

		batch = get_entered_batch(conn,atoi(PQgetvalue(result,i,4)));
		
		if (batch->b.num_papers == 0 ) {
			unentered++;
			continue;
		}
		/* DDS3.30: Find Errors in Batch */
		bwe = find_errors_in_batch(conn,batch,
                                           electorate_name);		
		next_batch = false;
		
		/* Have a look at each paper for an UNENTERED error code*/
		for (j=0;j < bwe->b.num_papers;j++) {
		        /* Increment appropriate counter */
		        if  (bwe->papers[j].error_code == ENTRY_ERR_UNENTERED) {
			        next_batch = true;
				once_entered++;
				break;
			}
			
		}
		/* move on to next batch */
		if (next_batch == true) continue;
		
		/* Have a look at each paper for a KEYSTROKE  error code*/
		for (j=0;j < bwe->b.num_papers;j++) {
		        /* Increment appropriate counter */
		        if  (bwe->papers[j].error_code == ENTRY_ERR_KEYSTROKE) {
			        next_batch = true;
				keystroke++;
				break;
			}
			
		}
		/* move on to next batch */
		if (next_batch == true) continue;

		/* Have a look at each paper for an  IGNORED,INFORMAL,
		   MISSING_NUM,DUPLICATED_NUM error code
		   which is NOT approved. i.e. does not have a supervisor tick
		*/
		for (j=0;j < bwe->b.num_papers;j++) {
		        if  ((bwe->papers[j].error_code == ENTRY_ERR_IGNORED ||
			     bwe->papers[j].error_code == ENTRY_ERR_INFORMAL ||
			     bwe->papers[j].error_code == ENTRY_ERR_MISSING_NUM ||
			     bwe->papers[j].error_code == ENTRY_ERR_DUPLICATED_NUM) &&
			     bwe->papers[j].p.supervisor_tick == false) {
			        next_batch = true;
				unapproved++;
				break;
			}
		}
		/* move on to next batch */
		if (next_batch == true) continue;
	

	/* NO errors found in papers? Batch status must be UNCOMMITTED*/
	if (j >= bwe->b.batch_size)
	        uncommitted++;

	free_batch(batch);
	free_batch_with_error(bwe);

	} /* for each batch */

	/* Write final counter values */
	if ( batches > 0 )
	        fprintf(fp,"\t\t%u\t%u\t%u\t%u\t%u\t%u\n",
			committed,unentered,once_entered,
			keystroke,unapproved,uncommitted);
	PQclear(result);
	fclose(fp);
	printfile(tmpfile);
	printf("Batch Summary Printed\n");
}

/* DDS3.28: Store Committed Batch Number */
static void store_comm_batch_num(PGconn *conn,unsigned int batch_number)
/*
  Adds a batch to the committed batch number store.
*/
{
	SQL_command(conn,
		    "UPDATE batch "
		    "SET committed = true "
		    "WHERE number = %u;",batch_number);
}


/* DDS3.28: Commit Votes */
static void commit_votes(PGconn *conn,unsigned int batch_number,
			   struct normalised_preference *np)
/*
  Saves the Normalised Preferences to the Confirmed Vote details store
  and adds the batch number to the confirmed votes store.
*/
{
	struct electorate *electorate = 
		(struct electorate *)  get_voter_electorate();
	int polling_place_code, i;
	unsigned int electorate_code = electorate->code;
	char *electorate_name = electorate->name;
	/* SIPL 2011-09-26 Increase array size by one to allow
	   space for null at end, to cope with the case where there
	   really are PREFNUM_MAX preferences in the vote. */
	char preference_string[PREFNUM_MAX * DIGITS_PER_PREF + 1],
		*pref_ptr, *p;
	char  *timestamp = generate_sortable_timestamp();

	fprintf(stderr, "\nEntered commit_votes\n");
	fprintf(stderr, "   batch_number %u\n", batch_number);

	fprintf(stderr,
		"\nIssue sql query: SELECT polling_place_code "
		"FROM batch WHERE number = %u;",
		batch_number);

	polling_place_code = 
		SQL_singleton_int(conn,
				  "SELECT polling_place_code "
				  "FROM batch WHERE number = %u;",
				  batch_number);
	
	if (polling_place_code == -1)
		bailout("Can't resolve polling place for batch %u\n", 
			batch_number);
	/* Begin the transaction */
	begin(conn);
	
	/* Prevent race condition in SELECT - INSERT or UPDATE code */
	SQL_command(conn,"LOCK TABLE vote_summary IN EXCLUSIVE MODE;");
	SQL_command(conn,"LOCK TABLE preference_summary IN EXCLUSIVE MODE;");

	/* Build vote for each set of prefs in normalised preferences list */
	for(np=np; np; np=np->next) {
		update_vote_summary(conn,np,polling_place_code, electorate_code);
		/* Store preferences for vote in <elec>_confirmed_vote  table */
		/* first build up preference string */
		pref_ptr = &preference_string[0];

		/* start with empty preference string */
		strcpy(pref_ptr,(const char *) "");
		for (i=0;i < np->n.num_preferences;i++) {
			p = sprintf_malloc("%02u%02u%02u",
					   np->preferences[i].prefnum,
					   np->preferences[i].group_index,
					   np->preferences[i].db_candidate_index
				);
			strcpy(pref_ptr,p);
			pref_ptr +=  (sizeof(char)*(DIGITS_PER_PREF));
			free(p);
			
			/* Summarise first preferences for election night */
			update_preference_summary(conn,
						  &np->preferences[i],
						  polling_place_code, 
						  electorate_code);
		}
	
	/* Store vote in confirmed vote table */
		fprintf(stderr,
			"\nIssue sql command: INSERT INTO "
			"%s_confirmed_vote (batch_number, time_stamp, "
			"paper_version, preference_list) "
			"VALUES(%u, '%s', %u, '%s');",
			electorate_name,
			batch_number,
			timestamp,
			np->n.paper_version,
			&preference_string[0]);

		SQL_command(conn,
			    "INSERT INTO %s_confirmed_vote "
			    "(batch_number, time_stamp, paper_version, "
			    "preference_list) "
			    "VALUES(%u,'%s',%u,'%s');",
			    electorate_name,
			    batch_number,
			    timestamp,
			    np->n.paper_version,
			    &preference_string[0]);
	
	}
	/* Store committed batch number */
	store_comm_batch_num(conn,batch_number);
	/* End the transaction */
	commit(conn);
	free(timestamp);

	printf("Batch %u committed for counting.\n", batch_number);
	fprintf(stderr, "Batch %u committed for counting.\n", batch_number);
	fprintf(stderr, "Leaving commit_votes\n");
}

/* DDS3.26: Normalise Preferences */
static void normalise_prefs(struct preference p_out[],
			    unsigned int *num_prefs_out,
			    struct preference p_in[],
			    unsigned int num_prefs_in)
/*
  Returns a list of prefernces which have Preference Indexes in ascending
  order starting from one with no missing numbers.
*/
{
	unsigned int prefnum=1,i,j=0,count;
	
	while (1) {
		/* Count number of time prefnum appears */
		count = 0;
		for (i=0;i<num_prefs_in;i++)
			if (p_in[i].prefnum == prefnum) {
				j = i;
				count++;
			}
		/* If only once - then copy across */
		if ( count == 1 ) {
			p_out[prefnum-1].prefnum = p_in[j].prefnum;
			p_out[prefnum-1].group_index = p_in[j].group_index;
			p_out[prefnum-1].db_candidate_index = 
				p_in[j].db_candidate_index;
			prefnum++;
		}
		else /* zero or more than one - exit loop */
			break;
	}

	*num_prefs_out = prefnum - 1;
}

/* DDS3.26: Normalise Batch */
static struct normalised_preference *normalise_batch(
	struct matched_preference *mp)
/*
  Returns a list of preferences which have Preference Indexes in ascending
  order starting from one with no missing numbers.
*/
{
	struct matched_preference *p;
	struct normalised_preference *np,*head=NULL;

	for (p=mp;p;p=p->next) {
		np = malloc(sizeof(*np) + 
			    sizeof(np->preferences[0])*p->m.num_preferences);
		normalise_prefs(&np->preferences[0],&np->n.num_preferences,
				&p->preferences[0],p->m.num_preferences);
		np->n.paper_version = p->m.paper_version;
		np->next = head;
		head = np;
	}
	return(head);
}

/* DDS3.26: Make Matched Preferences */
static struct matched_preference *make_match_prefs(PGconn *conn,
						   unsigned int batch_number)
/*
  Returns a list of corrected votes.
*/
{
	struct matched_preference *mp=NULL,*head=NULL;
	PGresult *result;
	unsigned int num_rows,num_prefs,i,entry_id,paper_index,paper_version;
	char *preference_list;
	char *electorate_name=(char *) get_voter_electorate()->name;
	
	fprintf(stderr, "\nEntered make_match_prefs\n");
	fprintf(stderr, "   batch number is %u\n", batch_number);

	/* Get last entry for each paper in batch up to batch-size entries
	 ALL REMAINING ENTRIES ARE APPROVED IGNORED PAPERS */
	fprintf(stderr,
		"\nIssue sql query: SELECT e.id, e.num_preferences, p.index,"
		"e.paper_version, preference_list "
		"FROM %s_entry e, %s_paper p, batch b, electorate el "
		"WHERE p.batch_number = %u "
                  "AND e.paper_id = p.id "
                  "AND e.index = ( SELECT MAX(index) FROM %s_entry "
		                   "WHERE paper_id = e.paper_id ) "
                  "AND b.number = p.batch_number "
                  "AND el.code  = b.electorate_code "
                  "AND p.index <= b.size;",
		electorate_name,
		electorate_name,
		batch_number,
		electorate_name);

	result = SQL_query(conn,
			   "SELECT e.id,e.num_preferences,p.index,"
			   "e.paper_version,preference_list "
			   "FROM %s_entry e, %s_paper p, batch b,electorate el "
			   "WHERE p.batch_number = %u "
			   "AND e.paper_id = p.id "
			   "AND e.index = ( SELECT MAX(index) "
			                   "FROM %s_entry "
			                   "WHERE paper_id = e.paper_id ) "
			   "AND b.number = p.batch_number "
			   "AND el.code = b.electorate_code "
			   "AND p.index <= b.size;",
			   electorate_name, electorate_name, 
			   batch_number,electorate_name);

	num_rows = PQntuples(result);
	fprintf(stderr, "num_rows is %d\n", num_rows);

	for (i=0;i<num_rows;i++) {
	  /* Dont commit ignored papers */
	  
		entry_id = atoi(PQgetvalue(result,i,0));
		num_prefs = atoi(PQgetvalue(result,i,1));
		paper_index = atoi(PQgetvalue(result,i,2));
		paper_version = atoi(PQgetvalue(result,i,3));
		preference_list=PQgetvalue(result,i,4);

		fprintf(stderr, "processing row %d\n", i);
		fprintf(stderr, "  entry_id: ...... %d\n", entry_id);
		fprintf(stderr, "  num_prefs: ..... %d\n", num_prefs);
		fprintf(stderr, "  paper_index: ... %d\n", paper_index);
		fprintf(stderr, "  paper_version: . %d\n", paper_version);
		fprintf(stderr, "  preference_list: '%s'\n", preference_list);

		/* Allocate space for next matched preference entry */
		mp = malloc(sizeof(*mp) + 
			    sizeof(mp->preferences[0])*num_prefs);

		get_prefs_for_entry(entry_id,num_prefs,&mp->preferences[0],
				    preference_list);

		mp->m.paper_index = paper_index;
		mp->m.num_preferences = num_prefs;
		mp->m.paper_version = paper_version;

		mp->next = head;
		head = mp;
	}
	return(head);
}


/* DDS3.26: Check Paper */
static bool check_paper(struct paper_with_error *pwe)
/*
  Returns true if the paper has: been entered twice, has no keystroke errors,
  and all ignored, informal, missing preference number and duplicate preference
  number papers have a supervisor tick. Otherwise false is returned.
*/

{
	fprintf(stderr, "\nEntered check_paper\n");

	switch (pwe->error_code) {
	case ENTRY_ERR_UNENTERED:
		printf("This batch has not been entered twice.\n");
		fprintf(stderr, "This batch has not been entered twice.\n");
		return false;

	case ENTRY_ERR_KEYSTROKE:
		printf("This batch has uncorrected keystroke errors.\n");
		fprintf(stderr, "This batch has uncorrected "
			"keystroke errors.\n");
		return false;

	case ENTRY_ERR_IGNORED:
		if (pwe->p.supervisor_tick == false) {
		  printf("This batch has ignored papers: change batch size\n");
		  fprintf(stderr, "This batch has ignored papers: "
			  "change batch size\n");
		  return false;
		}
		break;
	case ENTRY_ERR_INFORMAL:
	case ENTRY_ERR_MISSING_NUM:
	case ENTRY_ERR_DUPLICATED_NUM:
	        if (pwe->p.supervisor_tick == false) {
			printf("This batch has papers requiring "
			       "Supervisor approval.\n");
			fprintf(stderr, "This batch has papers "
				"requiring Supervisor approval.\n");
		        return false;
		}
		break;

	case ENTRY_ERR_CORRECT:
	case ENTRY_ERR_CORRECTED:
		break;
	case ENTRY_ERR_INVALID_BATCH_APPROVAL:
	  printf("Supervisor %s entered both active versions of a paper.\n"
             "Another Supervisor needs to approve this batch.\n",
             get_operator_id());
	  fprintf(stderr,
		  "Supervisor %s entered both active versions of a paper.\n"
		  "Another Supervisor needs to approve this batch.\n",
		  get_operator_id());
	  return false;
          break;
	}
	fprintf(stderr, "Leaving check_paper\n");
	return true;
}

/* DDS3.26: Extract Preferences */
static bool extract_preferences(PGconn *conn,
				struct batch_with_error *bwe,
				struct matched_preference **mp)
/*
  Returns Matched Preferences if all papers in the batch have: been entered
  twice, have no keystroke errors, and all ignored, informal, missing
  preference number and duplicate preference number papers have a 
  supervisor tick. Otherwise return false.
*/
{
	unsigned int i;
	bool edit_OK=false;

	fprintf(stderr, "\nEntered extract_preferences (EP)\n");

	fprintf(stderr,
		"EP: number of papers (bwe->b.num_papers) is %d\n",
		bwe->b.num_papers);

	fprintf(stderr,
		"EP: batch size (bwe->b.batch_size) is %d\n",
		bwe->b.batch_size);

	for(i=0;i<bwe->b.num_papers;i++) {
		if ((edit_OK = check_paper(&bwe->papers[i])) == false) {
			bwe->b.first_erroneous_paper_index=i+1;
			fprintf(stderr, "EP: check failed\n");
			break;
		}
	}

	if (edit_OK)
		*mp = make_match_prefs(conn,bwe->b.batch_number);
	else
		*mp = NULL;

	return(edit_OK);
}

/* DDS3.26: Commit Batch */
void commit_batch(PGconn *conn,unsigned int batch_number,
                  unsigned int electorate_code)
/*
  Commits a batch if all papers in the batch have been entered twice, have no
  keyboard errors, and all ignored, informal, missing preference number and
  duplicate number papers have a supervisor tick.
*/
{
	struct batch_with_error *bwe;
	struct batch *batch;
	struct matched_preference *mp;
	struct normalised_preference *np;
	unsigned int erroneous_paper;
	char *electorate_name;
	char *operator_id;

	fprintf(stderr, "\nEntered commit_batch (CB)\n");
	fprintf(stderr, "    batch_number .. %u\n", batch_number);
	fprintf(stderr, "    electorate_code %u\n", electorate_code);

	electorate_name = resolve_electorate_name(conn, electorate_code);
	operator_id = get_operator_id();

	fprintf(stderr, "\nCB: electorate_name is %s\n", electorate_name);
	fprintf(stderr, "CB: operator_id     is %s\n", operator_id);

	batch = get_entered_batch(conn,batch_number);
	/* DDS3.30: Find Errors in Batch */
	bwe = find_errors_in_batch(conn,batch,electorate_name);

	/* Don't allow a batch to be committed where the number of papers is */
        /* NOT equal to the batch size 	*/
	if (bwe->b.num_papers < bwe->b.batch_size) {
		printf("Batch %u cannot be committed. The number "
		       "of papers it contains (%u) is less than the declared " 
		       "batch size (%u).\nEither reduce the batch size to %u "
		       "or append paper(s) after %u\n",
		       batch_number,
		       bwe->b.num_papers,
		       bwe->b.batch_size,
		       bwe->b.num_papers,
		       bwe->b.num_papers );
	} else if (!check_operator_ids_ok (conn,
                                           batch_number,
                                           electorate_name,
                                           operator_id)) {
          printf("\nBatch %u cannot be committed.\n"
                 "You (%s) entered both entries of at least one paper.\n"
                 "Another Supervisor needs to commit this batch.\n",
                 batch_number, operator_id);
	} else if (extract_preferences(conn,bwe,&mp)) {
		np = normalise_batch(mp);
		commit_votes(conn,batch_number,np);
		log_batch_operation(conn,batch_number,(enum batch_op) COMMIT,
				    0,0);
	} else {
		erroneous_paper=bwe->b.first_erroneous_paper_index;
		log_batch_operation(conn,batch_number,(enum batch_op) COMMIT,
				    erroneous_paper,
				    bwe->papers[erroneous_paper-1].error_code);
	  printf("That batch cannot be committed yet because it contains "
		 "ignored, unentered, uncorrected or unapproved papers.\n");
	}
	free_batch(batch);
	free_batch_with_error(bwe);
}

/* DDS3.2: ? */
static void batch_size_prompt(void)
/*
  Print a text prompt.
*/
{
	printf("Please enter the new batch size: ");
}

/* DDS3.2: ? */
static unsigned int get_user_batch_size()
/*
  Obtain an batch size from the supervisor.
*/
{
	char *line;
	unsigned int b_size;

	batch_size_prompt();
	line = fgets_malloc(stdin);
	b_size = (unsigned int)atoi(line);
	free(line);
	return(b_size);
}

/* DDS3.24: Change Batch Size */
void chng_batch_size(PGconn *conn,unsigned int batch_number)
/*
  Allows a supervisor to change the size of a batch.
*/
{
	unsigned int new_batch_size,old_batch_size;

	/* Get the old and new batch size */
	old_batch_size = get_batch_size(conn, batch_number);
	new_batch_size = get_user_batch_size();

	/* Update the batch size */
	SQL_command(conn,
		    "UPDATE batch "
		    "SET size = %u "
		    "WHERE number = %u;",new_batch_size,batch_number);
	/* log the operation if the batch size has been changed from a non-zero
	   value */
	if (old_batch_size != 0)
		log_batch_operation(conn, batch_number, (enum batch_op) SIZE,
				    (int) old_batch_size,(int) new_batch_size);
}

/* delete the last paper with <entry_index> in <batch_number>   */
/* archive the destroyed details in the 'duplicate_entries' table */
void remove_paper(PGconn *conn,
			 const char *electorate_name,
			 unsigned int batch_number,
			 unsigned int archived_paper_index)

{
	PGresult *result;
	int paper_id, paper_index,batch_size;
	unsigned int num_entries,i,batch_history_id;
	unsigned int entry_id=0, entry_index=0,paper_version=0;
	char *operator_id=(char *) "", *preference_list=(char *) "";

	fprintf(stderr, "\nEntered remove_paper\n");
	fprintf(stderr, "    electorate_name .... '%s'\n", electorate_name);
	fprintf(stderr, "    batch_number ....... %u\n", batch_number);
	fprintf(stderr, "    archived_paper_index %u\n", archived_paper_index);

	/* find paper index of paper to be deleted */
	paper_index =  SQL_singleton_int(conn,
					 "SELECT MAX(index) "
					 "FROM %s_paper "
					 "WHERE batch_number = %u;",
					 electorate_name,
					 batch_number);
	fprintf(stderr, "paper_index is %d\n", paper_index);
	assert (paper_index > 0);

	/* get declared size of batch */
	batch_size = get_batch_size(conn,batch_number);
	fprintf(stderr, "batch_size is %d\n", batch_size);
	
	/* Delete all entries of last paper if it is greater than batch_size */
	if (paper_index > batch_size) {
		
		/* find unique id of paper to be deleted */
		paper_id = SQL_singleton_int(conn,
					     "SELECT id "
					     "FROM %s_paper "
					     "WHERE batch_number = %u "
					     "AND index = %d; ",
					     electorate_name,
					     batch_number, 
					     paper_index);
		fprintf(stderr, "paper_id is %d\n", paper_id);
		
		assert(paper_id > 0);
		
		/* retrieve and delete all entries of this paper */
		result = SQL_query(conn,
				   "SELECT e.id,e.index,e.operator_id, "
				   "e.paper_version,e.preference_list, p.index "
				   "FROM %s_paper p, %s_entry e "
				   "WHERE e.paper_id = p.id "
				   "AND p.id = %d; ",
				   electorate_name, electorate_name,
				   paper_id
			);
		
		num_entries = PQntuples(result);
		assert(num_entries > 0);
		
		for (i=0; i< num_entries; i++) {
			/* delete this entry */
		  fprintf(stderr, "Deleting the following entry\n");
		  fprintf(stderr, "    entry_id ...... %u\n",   entry_id);
		  fprintf(stderr, "    entry_index ... %u\n",   entry_index);
		  fprintf(stderr, "    operator_id ... '%s'\n", operator_id);
		  fprintf(stderr, "    paper_version . %u\n",   paper_version);
		  fprintf(stderr, "    preference_list '%s'\n",
			  preference_list);
		  fprintf(stderr, "    paper_index ... %d\n",   paper_index);

			entry_id        = atoi(PQgetvalue(result,i,0));
			entry_index     = atoi(PQgetvalue(result,i,1));
			operator_id     = PQgetvalue(result,i,2);
			paper_version   = atoi(PQgetvalue(result,i,3));
			preference_list = PQgetvalue(result,i,4);
			paper_index     = atoi(PQgetvalue(result,i,5));

			/* record in batch_history. We do this first because the archived 
			   entry will reference the batch_history id */
			log_batch_operation(conn,batch_number,(enum batch_op) DESTROY,
					    (int) paper_index,(int)  entry_index);
			
			batch_history_id=get_seq_currval(conn,"batch_history_id_seq");

			/* archive duplicate*/
			fprintf(stderr,
				"Archive entry, batch_history_id %u\n",
				batch_history_id);

			SQL_command(conn,
				    "INSERT into duplicate_entries(history_id,batch_number,"
				    "paper_index, entry_index, operator_id, paper_version,"
				    "preference_list) VALUES (%u,%u,%u,%u,'%s',%u,'%s');",
				    batch_history_id, batch_number, paper_index,
				    entry_index,operator_id,
				    paper_version,
				    preference_list
				);
			/* delete entry from table */
			fprintf(stderr,
				"Delete entry from table entry_id %u, %s\n",
				entry_id, electorate_name);

			SQL_command(conn,
				    "DELETE FROM %s_entry where id=%d;",
				    electorate_name,entry_id
				);
		}
		
		/* now delete the paper itself */
		fprintf(stderr,
			"Delete paper paper_id %d for '%s'\n",
			paper_id, electorate_name);
		SQL_command(conn,
			    "DELETE FROM %s_paper where id=%d;",
			    electorate_name,
			    paper_id);

		PQclear(result);
	}
	fprintf(stderr, "Leaving remove_paper\n");
	
	
}

/* DDS3.10: Prompt for Paper Index */
static void prompt_for_pi(void)
/*
  Print a text prompt.
*/
{
	printf("Please enter the paper index: ");
}

/* DDS3.10: Get Paper Index from User */
static unsigned int get_user_pi()
/*
  Obtain a Paper Index from the User.
*/
{
	char *line;
	unsigned int p_index;

	prompt_for_pi();
	line = fgets_malloc(stdin);
	p_index = (unsigned int)atoi(line);
	free(line);
	return(p_index);
}

/* DDS3.10: Set Paper Index */
bool set_paper_index(PGconn *conn,
			    unsigned int batch_number,
			    unsigned int *paper_id,
			    unsigned int *paper_index)
/*
  Obtains a Paper Index from the user.
*/
{
	unsigned int p_index;
	unsigned int p_id;
        struct electorate *electorate= 
		(struct electorate *) get_voter_electorate();

	p_index = get_user_pi();

	/* DDS3.2: Is Paper Index in Entered Batch Details */
	if ((p_id = SQL_singleton_int(conn,
			  "SELECT id FROM %s_paper "
			  "WHERE batch_number = %u "
			  "AND index = %u;",
				      electorate->name,
				      batch_number,p_index)
		    ) == -1) {
		/* DDS3.2: Paper Index Warning */
		printf("Paper Index invalid.\n");
		return(false);
	}
	*paper_id = p_id;
	*paper_index = p_index;
	set_current_paper_index(p_index);
	return(true);
}
/* DDS3.16: Prompt for Entry Index */
static void entry_index_prompt(void)
/*
  Print a text prompt.
*/
{
	printf("Please enter the entry index: ");
}

/* DDS3.16: Get Entry Index from User */
unsigned int get_user_entry_index(void)
/*
  Obtain an Entry Index from the User.
*/
{
	char *line;
	unsigned int p_index;

	entry_index_prompt();
	line = fgets_malloc(stdin);
	p_index = (unsigned int)atoi(line);
	free(line);
	return(p_index);
}

/* DDS3.16: Set Entry Index */
bool set_entry_index(PGconn *conn,unsigned int paper_id,
			    unsigned int *entry_index,char *operator_id)
/*
  Obtains a Entry Index from the user. If it's valid then also return the
  operator id for that entry.
*/
{
	unsigned int e_index;
	char *o_id;
	char *electorate_name=(char *) get_voter_electorate()->name;

	fprintf(stderr, "\nEntered set_entry_index\n");
	fprintf(stderr, "    paper_id ...... %u\n", paper_id);
	fprintf(stderr, "    electorate_name '%s'\n", electorate_name);

	e_index = get_user_entry_index();
	fprintf(stderr, "e_index is %u\n", e_index);

	/* DDS3.16: Is Entry Index in Entered Batch Details */
	if ((o_id = SQL_singleton(conn,
				  "SELECT operator_id FROM %s_entry "
				  "WHERE paper_id = %u "
				  "AND index = %u;",
				  electorate_name,
				  paper_id,e_index)) == NULL) {
		/* DDS3.16: Invalid Entry Index */
	  fprintf(stderr,
		  "ERROR: entry_index is invalid (paper: %u, ix: %u).\n",
		  paper_id, e_index);

		printf("Entry Index invalid (paper: %u, ix: %u).\n", 
		       paper_id,e_index);
		
		*entry_index=e_index;
		fprintf(stderr, "o_id is '%s'\n", o_id);

		return(false);
	}
	/* Load dynamic parameter return values */
	*entry_index=e_index;
	strcpy(operator_id,o_id);
	free(o_id);
	fprintf(stderr,
		"Leaving set_entry_index, entry_index to %u, "
		"operator_id to %s\n",
		e_index,
		o_id);
	return(true);
}

/* DDS3.12: Get Last Preferences 
 Modified: Don't get last entry - ask operator for entry index*/
static struct entry *get_entry_prefs(PGconn *conn,unsigned int batch_number,
				     unsigned int electorate_code,
				     unsigned int paper_index,
				     unsigned int entry_index)
/*
  Returns an entry containing the list of preferences from the highest
  entry index.
*/
{
	PGresult *result;
	struct entry *this_entry;
	struct electorate *electorate=
		(struct electorate *) get_voter_electorate();
	char *electorate_name=electorate->name;

	/* Get the details for the requested entry of this paper */
	result = SQL_query(conn,
			   "SELECT e.id,e.index,e.num_preferences,"
			   "e.preference_list "
			   "FROM %s_entry e, %s_paper p "
			   "WHERE p.batch_number = %u "
			   "AND p.index = %u "
			   "AND e.paper_id = p.id "
			   "AND e.index = %u;",
			   electorate_name, electorate_name,
			   batch_number,paper_index,entry_index);
	/* sanity check - only one row returned */
	assert (PQntuples(result) == 1 );

	/* Allocate space for this entry */
	this_entry = malloc(sizeof(*this_entry) + 
			    sizeof(this_entry->preferences[0]) *
			    atoi(PQgetvalue(result,0,2)));
	electorate_name = resolve_electorate_name(conn,electorate_code);
	/* And populate it with preferences */
	/* DDS3.2: Store Preferences */
	this_entry->e.index= atoi(PQgetvalue(result,0,1));
	this_entry->e.num_preferences = atoi(PQgetvalue(result,0,2));
	get_prefs_for_entry(atoi(PQgetvalue(result,0,0)),
			    atoi(PQgetvalue(result,0,2)),
			    &this_entry->preferences[0],
			    PQgetvalue(result,0,3));

	PQclear(result);
/*	free(electorate_name);*/
	return(this_entry);
}


/* DDS3.12: Store Preferences */
static void store_pref(struct entry *current_entry)
{
	unsigned int i;

     

	/* Populate the vote in progress with the current preferences */
	for (i=0; i<current_entry->e.num_preferences; i++) {
		add_candidate_with_pref(current_entry->preferences[i]
					.group_index,
					current_entry->preferences[i]
					.db_candidate_index,
					current_entry->preferences[i].prefnum);
	}
}


/* DDS3.12: Populate Vote in Progress */
static int pop_votes(PGconn *conn,unsigned int batch_number,
		     unsigned int electorate_code,
		     unsigned int paper_index,
		     unsigned int entry_index)
/*
  Fill the vote in progress store with the last entry of the current batch
  and current index.
*/
{
	struct entry *current_entry;
       
	/* first clear all preferences which may already be there */
	delete_prefs();

	/* load entry from DB */ 
	current_entry = get_entry_prefs(conn,batch_number,electorate_code,
				      paper_index,entry_index);

	store_pref(current_entry);
	
	return(current_entry->e.index);
}


/* DDS3.20: Remove Supervisor Tick */
static void rm_sup_tick(PGconn *conn, unsigned int paper_id)		
{
	struct electorate *electorate=
		(struct electorate *) get_voter_electorate();

	SQL_command(conn,
		    "UPDATE %s_paper "
		    "SET supervisor_tick = false "
		    "WHERE id = %u;",
		    electorate->name,paper_id);
}


/* DDS3.6: Edit Paper */
void edit_paper(PGconn *conn,unsigned int batch_number,
		unsigned int electorate_code)
/*
  Lets the supervisor edit a paper.
*/
{
	unsigned int paper_index;
	unsigned int entry_index=-1;
	unsigned int paper_id;
	int active_entry1 = 0;
	int active_entry2 = 0;
	int old_entry_id = 0; /* will be 1 or 2 */
	unsigned int pvn;
	bool cancelled,entry_index_ok=false;
	struct electorate *electorate=
		(struct electorate *) get_voter_electorate();
	struct rotation *rotation;
	char operator_id[10];
	char *electorate_name=(char *) get_voter_electorate()->name;

	set_current_batch_number(batch_number);
	  
	/* DDS3.2: Store Paper Index */
	if (!set_paper_index(conn,batch_number,&paper_id,&paper_index))
		return;
	
	get_active_entries(conn, electorate->name, batch_number, paper_index,
			   &active_entry1, &active_entry2);

	while (entry_index_ok==false ) {
		entry_index_ok = set_entry_index(conn,
						 paper_id,
						 &entry_index,
						 (char *) &operator_id);
		if (entry_index == 0) break;

		if (entry_index_ok &&
		    entry_index != active_entry1 && 
		    entry_index != active_entry2) {
			printf("entry %u exists but is archived.\n"
			       "The active entries for batch %u, paper %u "
			       "are:\n\t%u\n\t%u\n",
			       entry_index, batch_number, paper_index,
			       active_entry1, active_entry2);
			
			entry_index_ok=false;	
		}  
	}
	/* entering an entry index of 0 allows user to exit operation */
	if (entry_index == 0) return;

	if      (entry_index == active_entry1) old_entry_id = -1;
	else if (entry_index == active_entry2) old_entry_id = -2;
	else                                   old_entry_id =  1;

	/* Populate vote in progress */
	entry_index = pop_votes(conn,batch_number,electorate_code,
				paper_index,entry_index);
	
	/* Need to set voter electorate and rotation first */
	pvn = get_paper_version();
	
   	rotation = fetch_rotation(conn, pvn, electorate->num_seats); 
	
	set_current_rotation(rotation); 

	cancelled = enter_paper();
	
	if (!cancelled) {
		confirm_paper(pvn);
		rm_sup_tick(conn, paper_id);
		fprintf(stderr,
			"edit_paper: About to call update_active_entries "
			"with entry_id1, "
			"entry_index is %d\n",
			entry_index);

		update_active_entries(conn,
				      batch_number,
				      paper_index,
				      old_entry_id,
				      electorate_name);
		log_batch_operation(conn,batch_number,(enum batch_op) EDIT,
				    (int) paper_index,(int) entry_index);
	}
	
}

/* DDS3.42: Has Supervisor Tick */
static bool has_sup_tick(PGconn *conn, unsigned int batch_number, 
		  unsigned int paper_index)
{
	struct electorate *electorate=
		(struct electorate *) get_voter_electorate();
	bool tick;
	
	tick = SQL_singleton_bool(conn, 
				  "SELECT supervisor_tick "
				  "FROM %s_paper "
				  "WHERE batch_number = %u "
				  "AND index = %u;",
				  electorate->name,batch_number, paper_index);
	return tick;
}

/* DDS3.42: Invalid Supervisor Tick */
static void sup_tick_warning(void)
{
	printf("The Specified paper has already been approved.\n");
}


/* DDS3.42: Add Supervisor Tick */
static void add_sup_tick(PGconn *conn, unsigned int batch_number, 
		  unsigned int paper_index)
{
	struct electorate *electorate = 
		(struct electorate *)get_voter_electorate();
	SQL_command(conn,
		    "UPDATE %s_paper "
		    "SET supervisor_tick = true "
		    "WHERE batch_number = %u "
		    "AND index = %u;",
		    electorate->name,
		    batch_number, paper_index);

}


/* DDS3.42: Approve Paper */
void app_paper(PGconn *conn, unsigned int batch_number)
{
        struct paper *paper_to_approve;
	struct paper_with_error pwe;
	PGresult *result;
	unsigned int paper_id, paper_index, batch_size;
	int active_entry1;
	int active_entry2;
	struct electorate *electorate =
          (struct electorate *)get_voter_electorate();

	if (!set_paper_index(conn, batch_number, &paper_id, &paper_index)) 
	        return;
	
	if (has_sup_tick(conn, batch_number, paper_index)) {
		sup_tick_warning();
	}
	else {   
	        result = SQL_query(conn,
			   "SELECT size FROM batch " 
			   "WHERE number = %u;", batch_number);
		batch_size = atoi(PQgetvalue(result, 0, 0));
	        paper_to_approve = get_paper(conn,batch_number , paper_index);

		pwe = find_errors_in_paper(conn,
                                           paper_to_approve,
					   paper_index,
                                           batch_number,batch_size,
                                        (char *)get_voter_electorate()->name); 

		switch (pwe.error_code) {
		case ENTRY_ERR_CORRECT:
		case ENTRY_ERR_CORRECTED:
		  printf("That paper is correct. Approval not needed.\n");
			break;
		case ENTRY_ERR_IGNORED:
                  get_active_entries(conn,
                                     electorate->name,
                                     batch_number,
                                     paper_index,
                                     &active_entry1,
                                     &active_entry2);

                  if ((active_entry1 == -1) && (active_entry2 == -1)
                      && (paper_index > batch_size)) {
                    /*
                      Special case resulting from the copying of papers
                      in an entry when a deletion occurs.

                      When a deletion occurrs, all of the papers in
                      the specified entry index are copied
                      to a new entry index with the exception of the
                      paper being deleted.
                      This means that there may be a entry with only
                      one paper in it.
                      If the paper index is greater than the number of papers
                      in the batch, then approve the
                      paper. (The paper will not be committed).
                    */
		    fprintf(stderr,
			    "Approving paper at index %u - there are "
			    "no active entries associated with this paper.\n",
			    paper_index);
                    add_sup_tick(conn, batch_number, paper_index);
                    printf("Ignored paper has been approved as it "
                           "has no active entries.");
                  } else
                    printf("Paper index (%u) greater than batch size(%u). "
                           " Change batch size.\n",
                           paper_index, batch_size);
                  break;

		case ENTRY_ERR_INFORMAL:
		case ENTRY_ERR_MISSING_NUM:
		case ENTRY_ERR_DUPLICATED_NUM:
		        add_sup_tick(conn, batch_number, paper_index);
		        printf("Paper Approved");
			break;
		case ENTRY_ERR_UNENTERED:
		        printf("That paper has not yet been entered twice\n");
			break;
		case ENTRY_ERR_KEYSTROKE:
		        printf("That paper has typing errors. "
			       "Please edit the paper to correct the errors\n");
			break;
		case ENTRY_ERR_INVALID_BATCH_APPROVAL:
			printf("The person approving the batch "
                               "has entered both entries "
                               "for a paper.\n"
                               "Please get another Supervisor to "
                               "commit this batch.\n");
                        break;
		}
		
				
	}
}

/* DDS3.4: Execute Menu Selection */
static void exe_menu_selection(PGconn *conn,char command,
			       unsigned int electorate_code)
/*
  Execute a menu selection.
*/
{
	unsigned int batch_number;
	unsigned int polling_place_code;

	switch (command) {
        case 'A':
          if (set_uncom_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("edit_paper");
            edit_paper(conn, batch_number, electorate_code);
            close_log_file();
          }
          break;

        case 'B':
          if (set_uncom_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("insert_paper");
            insert_paper(conn, batch_number);
            close_log_file();
          }
          break;

        case 'C':
          if (set_uncom_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("append_paper");
            append_paper(conn, batch_number);
            close_log_file();
          }
          break;

        case 'D':
          if (set_uncom_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("delete_duplicate_paper");
            delete_duplicate_paper(conn, batch_number, electorate_code);
            close_log_file();
          }
          break;

        case 'E':
          if (set_uncom_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("change_batch_size");
            chng_batch_size(conn, batch_number);
            close_log_file();
          }
          break;

        case 'F':
          if (set_uncom_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("commit_batch");
            commit_batch(conn, batch_number, electorate_code);
            close_log_file();
          }
          break;

        case 'G':
          open_log_file("print_batch_summary");
          print_batch_summary(conn);
          close_log_file();
          break;

        case 'H':
          if (set_polling_place(conn, &polling_place_code)) {
            open_log_file("print_pp_batches");
            print_pp_batches(conn, electorate_code, polling_place_code);
            close_log_file();
          }
          break;

        case 'I':
          if (set_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("print_batch_all_entries");
            print_batch(conn, batch_number, false);
            close_log_file();
          }
          break;

        case 'J':
          if (set_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("print_batch_active_entries");
            print_batch(conn, batch_number, true);
            close_log_file();
          }
          break;

        case 'K':
          if (set_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("print_errors_in_batch");
            print_errors_in_batch(conn, batch_number);
            close_log_file();
          }
          break;

        case 'L':
          if (set_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("approve_paper");
            app_paper(conn, batch_number);
            close_log_file();
          }
          break;

        case 'M':
          if (set_batch_num(conn, &batch_number, electorate_code)) {
            open_log_file("report_batch_history");
            report_batch_history(conn, batch_number);
            close_log_file();
          }
          break;

        case 'N':
          printer = ! printer;
          break;

        default:
          printf("ERROR: Unrecognised command = %c\n", command);
          break;
	}
}

/* DDS3.2: Write Menu */
static void write_menu(PGconn *conn,unsigned int electorate_code)
/*
  Print to screen.
*/
{
	char *electorate_name;

	electorate_name = resolve_electorate_name(conn,electorate_code);

	printf("\n\n------------------------------------------------\n");
	printf("Electorate of %s\n",electorate_name);
	printf("Output Device = %s\n",
	       printer?(const char *)"Printer":(const char *)"Screen");
	printf("------------------------------------------------\n\n");
	printf("Select one of the following activities by typing "
	       "the corresponding letter (A to N)\n");
	printf("A - Edit Paper\n");
	printf("B - Insert Paper to entry\n");
	printf("C - Append Paper to entry\n");
	printf("D - Delete Paper from entry\n");
	printf("E - Change Batch Size\n");
	printf("F - Commit Batch\n");
	printf("G - Print %s Batch Summary\n",electorate_name);
	printf("H - Print Batches for a Polling Place\n");
	printf("I - Print Batch (all entries)\n");
	printf("J - Print Batch (active entries only)\n");
	printf("K - Print Errors in Batch\n");
	printf("L - Approve Paper\n");
	printf("M - Print Batch History\n");
	printf("N - Toggle Output Device\n\n");
	printf("Enter Menu Selection: ");

	free(electorate_name);
}

/* DDS3.2: Get Command */
static char get_BEntry_command(PGconn *conn,unsigned int electorate_code)
/*
  Obtain the command selection.
*/
{
	char command;
	char *dummy;

     	do {
		write_menu(conn,electorate_code);
		command = toupper(getchar());
		/* Discard any further characters up to and including the newline. */
		dummy = fgets_malloc(stdin); 
		free(dummy);
	} while (command < 'A' || command > 'N');
	
	return(command);
}

/* DDS3.2: Electorate Warning */
static void elect_warning(void)
/*
  Print a text warning.
*/
{
	printf("Not a valid Electorate.\n\n");
}

/* DDS3.2: Prompt for Electorate */
static void electorate_prompt(void)
/*
  Print a text prompt.
*/
{
	printf("Please enter Electorate: ");
	
}

/* DDS3.2: Get Electorate Name from User */
static unsigned int get_user_elect(PGconn *conn)
/*
  Obtain a valid electorate from the user.
*/
{
	int e_code;
	char *electorate_name;
	struct electorate *electorate;

	do {
		electorate_prompt();
		electorate_name = fgets_malloc(stdin);
		if ((e_code = resolve_electorate_code(conn,electorate_name))
		    == -1) {
			elect_warning();
		}
	} while ( e_code == -1);

	electorate = malloc(sizeof(struct electorate)
                                  + strlen(electorate_name)+1);
	strcpy(electorate->name,electorate_name);

	electorate->code = e_code;
	electorate->num_seats 
		= (unsigned int)SQL_singleton_int(conn,
						  "SELECT seat_count "
						  "FROM electorate "
						  "WHERE code = %u;",
						  e_code);
	store_electorate(electorate);

	free(electorate_name);

	return((unsigned int)e_code);
}

/* DDS3.2: Set Electorate */
static unsigned int set_electorate(PGconn *conn)
/*
  Set the electorate code in the Batch Electorate store
*/
{
	return(get_user_elect(conn));
}

/* DDS3.2: Batch Edit */
void batch_edit(void)
/*
  Obtain electorate, display the batch edit menu, input and execute a 
  menu selection
*/
{
        char *operator_id=get_operator_id();
      	char command;
	unsigned int electorate_code;
	PGconn *conn;
	/* Sanity Check: operator must log in as a SUPERVISOR */
	if (strncmp(operator_id,"super",5) !=0) {
		fprintf(stderr, 
			"Fatal Error: Only Supervisors may correct ballots.\n"
			"You are logged in as %s.\n",operator_id);
		exit(1);
	} 
	    
	conn = connect_db_host(DATABASE_NAME,SERVER_ADDRESS);
	if (!conn) bailout ("Can't connect to database '%s' at %s",
			    DATABASE_NAME,SERVER_ADDRESS);
	electorate_code = set_electorate(conn);

	set_ballot_contents(get_electorate_ballot_contents(conn, 
							   electorate_code));

	while (1) {
		command = get_BEntry_command(conn,electorate_code);
		exe_menu_selection(conn,command,electorate_code);
	}

	PQfinish(conn);
}

