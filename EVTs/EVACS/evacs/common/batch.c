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

/* This file contains implementation of batch functionality*/
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <common/database.h>
#include <common/voter_electorate.h>
#include <common/find_errors.h>
#include <common/batch_history.h>

#include "batch.h"


/* batch number currently being operated on  */
static unsigned int current_batch;


unsigned int get_current_batch_number(void)
{
	return current_batch;
}

void set_current_batch_number(unsigned int batch_number)
{
	current_batch = batch_number;
}

int get_batch_size(PGconn *conn, 
		   unsigned int batch_number) 
{
	int batch_size;
	
	batch_size=SQL_singleton_int(conn,
				     "SELECT size FROM batch "
				     "WHERE number = %u;",
				     batch_number);
	return(batch_size);
}


/* DDS3.6: Get Entered Papers 
   from v2B */
struct batch *get_entered_batch(PGconn *conn, 
				unsigned int batch_number)
     /*
       Return all preferences for the given batch number
     */

{
	PGresult *result;
	struct batch *head=NULL, *tmp=NULL;
	struct predefined_batch *batch;
	char *electorate_name;
	unsigned int num_papers,electorate_code;

	/* get electorate code */
	batch = resolve_batch_source(conn, batch_number);
	electorate_code = batch->electorate_code;

	/* get electorate name in order to access that Electorates
	   preference table */
	electorate_name = resolve_electorate_name(conn,electorate_code);

	num_papers = (unsigned int )SQL_singleton_int(conn,
				      "SELECT COUNT(*) "
				      "FROM %s_paper "
				      "WHERE batch_number = %u;",
				      electorate_name, batch_number);

	/* build the batch structure */
	tmp = malloc(sizeof(*tmp) + (sizeof(tmp->papers[0]) * num_papers));

	tmp->b.batch_number = batch_number;

	result = SQL_query(conn,
			   "SELECT size, committed "
			   "FROM batch "
			   "WHERE number = %u;", batch_number);

	tmp->b.batch_size = atoi(PQgetvalue(result, 0, 0));
	tmp->b.num_papers = num_papers;

	if (*PQgetvalue(result,0,1) == 't')
		tmp->b.committed = true;
	else
		tmp->b.committed = false;

        /* papers and sub-structures inserted into tmp */
	if (num_papers > 0)
	        get_papers_for_batch(conn, tmp, electorate_name);

	tmp->next = NULL;
	head = tmp;

	
	PQclear(result);
	free(electorate_name);
        return head;
}

/* DDSv2C: Get Paper  */
struct paper *get_paper(PGconn *conn, 
			unsigned int batch_number, 
			unsigned int paper_index)

{
	struct paper *ret;
	unsigned int paper_id, electorate_code;
	char *electorate_name, *paper_table_name;
	struct predefined_batch *batch;

	/* get electorate code */
	batch = resolve_batch_source(conn, batch_number);
	assert(batch);
	electorate_code = batch->electorate_code;

	/* get electorate name in order to access that Electorates
	   paper and entry tables */
	electorate_name = resolve_electorate_name(conn,electorate_code);
	paper_table_name = sprintf_malloc("%s_paper",electorate_name);
	
	
	/* find the (internal database) paper_id */
	paper_id = SQL_singleton_int(conn,
				     "SELECT id "
				     "FROM %s "
				     "WHERE batch_number = %u "
				     "AND index = %u;",
				     paper_table_name, 
				     batch_number, paper_index);

	ret = malloc(sizeof(*ret));

	if (paper_id ==(unsigned int) -1) {
	  /* new paper  */
	    ret->p.index = paper_index;
	    ret->p.supervisor_tick = false;
	    ret->entries = NULL;
	} else {
	        ret = malloc(sizeof(*ret));
	        ret->entries = get_entries_for_paper(conn, paper_id,
						     electorate_name);
	}

	free(electorate_name);
	free(paper_table_name);
	free(batch);
	
	return ret;
}

void get_papers_for_batch(PGconn *conn, 
			  struct batch *batch,
			  char *electorate_name)
/* load the batch structure pointed to by batch with paper data*/
{
        unsigned int i;
	PGresult *result;
	unsigned int num_rows,paper_id;

	result =  SQL_query(conn,
			    "SELECT id, "
			    "index, "
			    "supervisor_tick "
			    "FROM  %s_paper "
			    "WHERE batch_number= %u "
			    "ORDER BY index;", 
			    electorate_name, batch->b.batch_number);
	
	num_rows = PQntuples(result);

	/*  build a return structure
	 */
	for (i=0;i<num_rows;i++) {
		paper_id = atoi(PQgetvalue(result, i, 0));
		batch->papers[i].p.index = atoi(PQgetvalue(result,i,1));
		batch->papers[i].p.supervisor_tick =  
			(*PQgetvalue(result, i, 2) == 't')?true:false;

		/* entries and sub-structures inserted into batch->papers */
		batch->papers[i].entries = get_entries_for_paper(conn,
					    paper_id,electorate_name);
	
	}
	PQclear(result);
	
}

static struct entry *new_entry(unsigned int num_prefs, const char *operid,
			       unsigned int index, unsigned int pvn)
{
	struct entry *ret;

	ret = malloc(sizeof(*ret) + sizeof(ret->preferences[0]) * num_prefs);
	ret->e.num_preferences = num_prefs;
	strcpy(ret->e.operator_id, operid);
	ret->e.paper_version_num = pvn;
	ret->e.index=index;
	return ret;
}

struct entry *get_entries_for_paper(PGconn *conn, 
				    unsigned int paper_id,
				    char *electorate_name)
/* load the paper structure pointed to by paper with entry data*/

{
	PGresult *result;
	struct entry *head = NULL, *tmp = NULL;
	unsigned int i, num_rows, entry_id;

	result =  SQL_query(conn,
			    "SELECT id,index,"
			    "operator_id,"
			    "num_preferences,"
			    "paper_version, preference_list "
			    "FROM  %s_entry "
			    "WHERE paper_id= %u "
			    "ORDER BY index DESC;",
			    electorate_name,paper_id);
	
	num_rows = PQntuples(result);
	
	/*  build a return structure
	 */
	for (i=0;i<num_rows;i++) {
		entry_id = atoi(PQgetvalue(result,i,0));      /* entry id  */
		tmp = new_entry(atoi(PQgetvalue(result,i,3)), /* num prefs */
				PQgetvalue(result,i,2),       /* operator  */
				atoi(PQgetvalue(result,i,1)), /* entry ix  */
				atoi(PQgetvalue(result,i,4)));/* pvn       */ 

      /* link the entries such that the last entry is at the head of the list */
		tmp->next = head;
		head = tmp;
	       
		get_prefs_for_entry(entry_id, 
				    atoi(PQgetvalue(result,i,3)),/* num_prefs */
				    &head->preferences[0],       /* 'out' var */
				    PQgetvalue(result,i,5));     /* pref list */
	}
	PQclear(result);

	return(head);
}

void get_prefs_for_entry(unsigned int entry_id, unsigned int num_preferences,
			 struct preference preferences[],
			 char *preference_list)
/* load the entry structure pointed to by entry with preference data*/

{
	unsigned int i, num_prefs;
	char *pref_ptr;

	for (pref_ptr=(char *)preference_list,num_prefs=0;
	     strlen(pref_ptr)>=DIGITS_PER_PREF;
	     pref_ptr += DIGITS_PER_PREF*sizeof(char),num_prefs++);
	
	if (num_prefs != num_preferences)
		bailout("database reports %u preferences for entry_id(%u), "
			"but found %u instead.",
			num_preferences, entry_id, num_prefs);

	/* Sanity Check: pref_ptr should be at end of string */
	if ( strlen(pref_ptr)) 
		bailout("malformed pref list entry_id(%u)\n'%s'\n",
			entry_id,preference_list);

	/* Decode preference list into memory structure */
	for (pref_ptr = preference_list, i = 0;
	     i < num_prefs; 
	     i++,pref_ptr += DIGITS_PER_PREF*sizeof(char) )
	{
		sscanf(pref_ptr,(const char *)"%2u%2u%2u",
		       &preferences[i].prefnum,
		       &preferences[i].group_index,
		       &preferences[i].db_candidate_index
			);
	}
	
}


void save_paper(struct paper *newpaper, 
		unsigned int batch_number)
{
        PGconn *conn = connect_db_host(DATABASE_NAME, SERVER_ADDRESS);
	struct predefined_batch *batch;
	char *electorate_name, *paper_table_name;
	unsigned int electorate_code;

	/* get electorate code */
	batch = resolve_batch_source(conn, batch_number);
	electorate_code = batch->electorate_code;

	/* get electorate name in order to access that Electorates
	   paper table*/
	electorate_name = resolve_electorate_name(conn,electorate_code);
	paper_table_name = sprintf_malloc("%s_paper",electorate_name);

	SQL_command(conn, 
		    "INSERT into %s(batch_number,index,supervisor_tick) "
		    "values(%u, %u, 'f');",
		    paper_table_name,
		    batch_number, 
		    newpaper->p.index);

	free(electorate_name);
	free(paper_table_name);
	free(batch);

	PQfinish(conn);
}

void append_entry(PGconn *conn,
		  struct entry *newentry,
		  unsigned int batch_number,
		  unsigned int paper_index)
     /*
       Insert the entry into the database.
     */
{	
	char *electorate_name, *entry_table_name, *paper_table_name;
        int  paper_id=-1;
        int temp;
	unsigned int i,entry_index;
	/* SIPL 2011-09-26 Increase array size by one to allow
	   space for null at end, to cope with the case where there
	   really are PREFNUM_MAX preferences in the vote. */
	char pref_string[DIGITS_PER_PREF * PREFNUM_MAX + 1];
	char *pref_ptr, *p;
	struct predefined_batch *batch;

	/* get electorate code */
        batch =resolve_batch_source(conn, batch_number);
	electorate_name = resolve_electorate_name(conn, batch->electorate_code);
	if (batch->electorate_code < 0)
		bailout("append_entry could not find batch number %u.\n",
			batch_number);

	/* get electorate name in order to access that Electorates'
	   paper and entry tables */
	paper_table_name = sprintf_malloc("%s_paper",electorate_name);	
	entry_table_name = sprintf_malloc("%s_entry",electorate_name);

	/* Start the transaction */
	begin(conn);

	/* check paper exists */
	paper_id = SQL_singleton_int(conn,
				     "SELECT id "
				     "FROM %s_paper "
				     "WHERE batch_number = %u "
				     "AND index = %u; ",
				     electorate_name,
				     batch_number,paper_index);

	/* Insert new paper if necessary */
	if (paper_id < 0) {
	        SQL_command(conn,
			    "INSERT INTO "
			    "%s(batch_number,index) "
			    "VALUES(%u,%u);",
			    paper_table_name,batch_number,paper_index);
		entry_index = 1;
		paper_id = 
			SQL_singleton_int(conn,"SELECT CURRVAL('%s_id_seq');",
					  paper_table_name);

	}
	else {
	        /* Get last (archived) entry index for this paper */
	        entry_index = SQL_singleton_int(conn,
						"SELECT MAX(index) FROM %s "
						"WHERE paper_id = %d;",
						entry_table_name, paper_id);
		if (entry_index < 0)
		        entry_index = 1;   /* It must be the first one */
		else
		        entry_index++;

	}
	
        if (entry_index == 1) {

          /* Check for the case there this is actually entry_index=2, and
             where there is no entry_index=1.
          */

          temp = (unsigned int)
            SQL_singleton_int(conn,
                              "SELECT MAX(e.index) "
                              "FROM %s_entry e, %s_paper p "
                              "WHERE p.batch_number = %u "
                              "AND e.paper_id     = p.id "
                              "AND e.operator_id  = '%s';",
                              electorate_name, electorate_name,
                              batch_number,    get_operator_id());
          if (temp == 2) {
            /* This paper's belongs to entry index 2, not 1. */
            entry_index = 2;
          }
        }

	/* Format the preferences into a string */
	pref_string[0]='\0';
	pref_ptr = &pref_string[0];
	for (i=0;i<newentry->e.num_preferences;i++) {
		p = sprintf_malloc("%02u%02u%02u",
				   newentry->preferences[i].prefnum,
				   newentry->preferences[i].group_index,
				   newentry->preferences[i].db_candidate_index
				   );
		strcpy(pref_ptr,p);
		pref_ptr +=  (sizeof(char)*(DIGITS_PER_PREF));
		free(p);
	}	
        /* Insert new entry into archive */
	SQL_command(conn,
		    "INSERT INTO %s(index,operator_id,"
		    "paper_id,num_preferences,paper_version,preference_list) "
		    "VALUES(%u,'%s',%u,%u,%u,'%s');",
		    entry_table_name, entry_index,
		    newentry->e.operator_id,
		    paper_id,newentry->e.num_preferences,
		    newentry->e.paper_version_num,
		    &pref_string[0]);

	/* update active entries */
	update_active_entries(conn,
			      batch_number,
			      paper_index,
			      1, // arbitrary, could be 2
			     (const char *)  electorate_name);

	free(electorate_name);
	free(paper_table_name);
	free(entry_table_name);
	free(batch);
	/* Complete the transaction */
	commit(conn);
}

extern void get_active_entries(PGconn *conn, 
			       const char *electorate_name, 
			       unsigned int batch_number, 
			       unsigned int paper_index,
			       int *active_entry1,
			       int *active_entry2) 
{
	PGresult *result;
	/* Check paper exists */
	result = SQL_query(conn,
			   "SELECT entry_id1,entry_id2 FROM %s_paper "
			   "WHERE index = %d "
			   "AND batch_number = %u;",
			   electorate_name, paper_index,batch_number
		);
	
	if (PQntuples(result) > 0 ) { 
		*active_entry1 = atoi(PQgetvalue(result,0,0));
		*active_entry2 = atoi(PQgetvalue(result,0,1));			
	} else {
		/* paper not found */
		active_entry1 = active_entry2 = 0;
	}
	PQclear(result);
}
extern void update_active_entries(PGconn *conn, 
			   unsigned int batch_number,
			   unsigned int paper_index,
			   int preferred_entry_to_replace,
			   const char *electorate_name)
{
	int temp;
	unsigned int num_entries,match_code,entry_to_replace;
	int paper_id;
	
	paper_id = SQL_singleton_int(conn,
				     "SELECT id "
				     "FROM %s_paper "
				     "WHERE batch_number = %u "
				     "AND index = %u; ",
				     electorate_name,
				     batch_number,paper_index);
	num_entries= (unsigned int)
		SQL_singleton_int(conn,
				  "SELECT MAX(e.index) "
				  "FROM %s_entry e,%s_paper p "
				  "WHERE p.batch_number = %u "
				  "AND e.paper_id = p.id "
				  "AND p.id = %u; ",
				  electorate_name,electorate_name,
				  batch_number,paper_id);
	
	/* if only 1 or two entries, make new entry active */
	if (num_entries < 3) {
		entry_to_replace = num_entries;
                if (entry_to_replace == 1) {

                  temp = (unsigned int)
                    SQL_singleton_int(conn,
                                      "SELECT MAX(e.index) "
                                      "FROM %s_entry e, %s_paper p "
                                      "WHERE p.batch_number = %u "
                                      "AND e.paper_id = p.id "
                                      "AND e.operator_id = '%s';",
                                      electorate_name, electorate_name,
                                      batch_number, get_operator_id());
                  if (temp == 2) {
                    entry_to_replace = temp;
                  }
                }
	} else {
		/* returns either matching active entry OR 
		 3 = both matched, 4 = neither matched*/
		match_code = 
			match_active_entries(conn,
					     (char *)electorate_name,
					     paper_id);
		if (match_code == 1 || match_code == 2) {
			/* only one active entry matched;  replace the other */
			entry_to_replace=(3-match_code);
		} else {
			if (strncmp(get_operator_id(),"super",5) ==0) {
			/* user is SUPER and either both or neither matched: */
			/* replace 1st active entry (arbitrary choice) */
	              if (preferred_entry_to_replace < 0)
                        entry_to_replace = (unsigned int)
                          (-1 * preferred_entry_to_replace);
                      else
                        entry_to_replace = (unsigned int)
                          preferred_entry_to_replace;
			} else {
				/* normal user and both or neither matched: */
				/* leave active entries unchanged */
				entry_to_replace = 0;
			}
		}
	}
        if (preferred_entry_to_replace < 0) {
          /*
            When preferred_entry_to_replace is less than zero, then
            abs(preferred_entry_to_be_replace) is to be used as the
            entry index.
          */

	  /* SIPL 2011-09-26 Add parentheses to adjust the "order" of
	     evaluation.  In fact, it makes no difference because
	     of two's complement arithmetic.  But it is now consistent
	     with the previous similar assignment statement. */
	  entry_to_replace = (unsigned int) (-1 * preferred_entry_to_replace);
        }

	/* do the replacement if required */
	if (entry_to_replace > 0) 
		replace_active_entry(conn, batch_number, paper_index,
				     electorate_name, 
				     paper_id, entry_to_replace, 
				     num_entries);
}


/* Allocate 'active' entry */
int replace_active_entry(PGconn *conn,
			 unsigned int batch_number,
			 unsigned int paper_index,
			 const char *electorate_name,
			 unsigned int paper_id, 
			 unsigned int active_entry_ix, /* 1 or 2 */
			 unsigned int entry_ix) {

	int num_rows_updated;
	char *entry_field_name = sprintf_malloc("entry_id%u",active_entry_ix);
	char *paper_table_name = sprintf_malloc("%s_paper",electorate_name);

	num_rows_updated = SQL_command(conn,
				       "UPDATE %s SET %s=%u WHERE id=%u;",
				       paper_table_name, 
				       entry_field_name,
				       entry_ix,
				       paper_id);

	assert (num_rows_updated == 1);
	/* record change in batch history after initial 2 entries */
	if (entry_ix > 2 ) 
		log_batch_operation(conn, batch_number,(enum batch_op) ACTIVE,
				    paper_index, entry_ix);
	free(entry_field_name);
	free(paper_table_name);
	
	return num_rows_updated;
}

/* DDS3.4: Resolve Batch Electorate 
   from v2B */
/* DDS3.6: Get Electorate Code from Predefined Batch Details
 from v2C*/
struct predefined_batch *resolve_batch_source(PGconn *conn, 
					      unsigned int batch_number) {
       /*
	 return the electorate code of the batch number
       */
       struct predefined_batch *batch;
       PGresult *result;
      
       result = SQL_query(conn, 
			  "SELECT electorate_code,polling_place_code "
			  "FROM batch WHERE number = %u;",
			  batch_number);

       if (PQresultStatus(result) != PGRES_TUPLES_OK) {
	       PQclear(result);
	       return NULL;
       }

       if (PQntuples(result) == 0) {
	       PQclear(result);
	       return NULL;
       }

       batch = malloc(sizeof(struct predefined_batch));
       batch->electorate_code = atoi(PQgetvalue(result,0,0));
       batch->polling_place_code = atoi(PQgetvalue(result,0,1));
       batch->batch_number = batch_number;

       /* make sure this struct knows its a singleton */
       batch->next = NULL;

       PQclear(result);

       return batch;
}



char *resolve_electorate_name(PGconn *conn, 
			      unsigned int electorate_code)

{
        return(SQL_singleton(conn,
			     "SELECT name FROM electorate WHERE code = %u;",
			     electorate_code));
}


int resolve_electorate_code(PGconn *conn,
			    const char *electorate_name)
{
	return(SQL_singleton_int(conn,
				 "SELECT code FROM electorate "
				 "WHERE UPPER(name) = UPPER('%s');",
				 electorate_name));
}

char *resolve_polling_place_name(PGconn *conn, 
				 unsigned int polling_place_code)

{
        return(SQL_singleton(conn,
			     "SELECT name FROM polling_place WHERE code = %u;",
			     polling_place_code));
}

int resolve_polling_place_code(PGconn *conn,
			       const char *polling_place_name)
{
	return(SQL_singleton_int(conn,
				 "SELECT code FROM polling_place "
				 "WHERE UPPER(name) = UPPER('%s');",
				 polling_place_name));
}

void log_batch_operation(PGconn *conn, unsigned int batch_number, 
			 enum batch_op opcode,
			 int data1, int data2)
{
	char *operator_id = get_operator_id();
	char *timestamp = generate_sortable_timestamp();

	SQL_command(conn,
		"INSERT INTO batch_history"
		"(batch_number,operator_id, time_stamp, op_code,data1,data2) "
		"values(%u, '%s', '%s', %u, %u, %u);",
	 batch_number, operator_id, timestamp, opcode, data1, data2);

	free(operator_id);
	free(timestamp);

}

void free_batch(struct batch *batch)
{
	unsigned int i;

	/* For every paper, free linked list of entries */
	for (i = 0; i < batch->b.num_papers ; i++) {
		while (batch->papers[i].entries) {
			struct entry *next;

			next = batch->papers[i].entries->next;
			free(batch->papers[i].entries);
			batch->papers[i].entries = next;
		}
	}

	free(batch);
}
