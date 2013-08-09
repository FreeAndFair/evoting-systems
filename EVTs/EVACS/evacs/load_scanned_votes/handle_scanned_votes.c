/* This file is (C) copyright 2008 Software Improvements, Pty Ltd */

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

#include <stdio.h>
#include <unistd.h>
/* For malloc() */
#include <stdlib.h>
/*#include <string.h>*/
#include <signal.h>
/* For memset() */
#include <string.h>

#include <common/evacs.h>
#include <common/database.h>
#include <common/ballot_contents.h>
#include <common/get_electorate_ballot_contents.h>
#include "handle_scanned_votes.h"
#include "scanned_votes.h"


/* Highest electorate code */
static int max_electorate=0;

/* These are used as arrays indexed by 1..max_electorate */
static struct electorate **electorates;
unsigned int electorates_length; /* Length of electorates in bytes */
static struct ballot_contents **all_ballot_contents;

/* Reporting data, also index by 1..max_electorate */
static struct reporting_data {
  unsigned int batches_imported;
  unsigned int papers_imported;
  unsigned int informal_papers;
} **reporting_data;

/* Highest number of groups in any electorate */
static int max_num_groups=0;

/* Highest number of candidates in any group in any electorate */
static int max_num_candidates=0;

/* It's too slow to increment first preference summaries
   for every single vote, so we do our own counting along
   the way and update the summaries whenever we see a new
   electorate/polling place in the data.
   Use first_preferences as though it were a two-dimensional
   array.  Access it thus:
   FIRST_PREFERENCES(group,candidate)
   Note: groups and candidates are indexed from 0.
   Use CLEAR_FIRST_PREFERENCES to reset the array.
*/

unsigned int *first_preferences;
unsigned int first_preferences_length;

#define FIRST_PREFERENCES(group,candidate) \
  first_preferences[(group*max_num_candidates)+candidate]
#define CLEAR_FIRST_PREFERENCES \
  memset(first_preferences,0,first_preferences_length)

/* Keep track of informal_count by electorate/polling place.
   Reset each time electorate/polling place is changed during
   filtering. */
unsigned int informal_count=0;


/* Temporary files containing the votes that will be
   loaded into the database. */
/* First, the array of filenames. */
char **vote_filenames;
/* Now, the array of files. */
FILE **vote_files;

static void setup_electorate_and_ballot_data(PGconn *conn) {
  struct electorate *elec_ptr, *elec_ptr_start;
  struct ballot_contents *ballot_cursor;
  unsigned int i;
  char tempfile_template[]="/tmp/evacsXXXXXXX";
  max_electorate = SQL_singleton_int(conn,"SELECT MAX(code) "
                                      "FROM electorate;");
  
  if (max_electorate < 0)
    bailout("There are no electorates defined!\n");

  /* Now we can allocate memory for the arrays. Add one in each case
     because we index the arrays starting at one.*/
  electorates_length = sizeof(struct electorate *) * (max_electorate + 1);
  electorates = malloc(electorates_length);
  memset(electorates,0,electorates_length);

  if (!electorates)
    bailout("Out of memory while allocating space for electorates!\n");

  all_ballot_contents = malloc(sizeof(struct ballot_contents *)
                               * (max_electorate + 1));
  if (!all_ballot_contents)
    bailout("Out of memory while allocating space for ballots!\n");

  reporting_data = malloc(sizeof(struct reporting_data *)
                          * (max_electorate + 1));
  if (!reporting_data)
    bailout("Out of memory while allocating space for report data!\n");

  /* get all electorate data */
  elec_ptr=get_electorates(conn);
  elec_ptr_start = elec_ptr;

  /* convert to arrays for lookups by code */
  for (;elec_ptr;elec_ptr=elec_ptr->next) {
    electorates[elec_ptr->code]=elec_ptr;
    /* Get ballot data for this electorate. */
    all_ballot_contents[elec_ptr->code] =
      get_electorate_ballot_contents(conn,elec_ptr->code);
    /* Examine ballot data */
    ballot_cursor = all_ballot_contents[elec_ptr->code];
    if (ballot_cursor->num_groups > max_num_groups)
      max_num_groups = ballot_cursor->num_groups;
    for (i = 0; i < ballot_cursor->num_groups; i++)
      if (ballot_cursor->num_candidates[i] > max_num_candidates)
        max_num_candidates = ballot_cursor->num_candidates[i];
    /* Allocate space for reporting data for this electorate. */
    reporting_data[elec_ptr->code] = malloc(sizeof(struct reporting_data));
    if (!reporting_data[elec_ptr->code])
      bailout("Out of memory while allocating space for report data!\n");
    memset(reporting_data[elec_ptr->code],0,sizeof(struct reporting_data));
  }

  /* Now we can create the first_preferences array.
   Don't forget to leave space for the electorate 0. */
  first_preferences_length = sizeof(unsigned int)
    * max_num_groups * max_num_candidates;
  first_preferences = malloc(first_preferences_length);


  /* Now setup temporary files to store votes */
  vote_filenames = malloc(sizeof(char *) * (max_electorate + 1));
  vote_files = malloc(sizeof(FILE *) * (max_electorate + 1));

  for (i=0; i<=max_electorate; i++) {
    int fd;
    if (electorates[i]) {
      vote_filenames[i] = malloc(sizeof(tempfile_template));
      if (!vote_filenames[i])
        bailout("Out of memory while allocating space for temporary "
                "file names!\n");
      strcpy(vote_filenames[i],tempfile_template);
      fd = mkstemp(vote_filenames[i]);
      if (fd < 0)
        bailout("Couldn't open temporary file!\n");
      close(fd);
      vote_files[i] = fopen(vote_filenames[i],"w");
      if (!vote_files[i])
        bailout("Couldn't open temporary file!\n");
    }
  }

}


/* Call this function before starting processing a new
   electorate/polling place to "flush" the summaries
   for the previous electorate/polling place.
   Call with electorate_code and polling_place_code both
   -1 to flush the last summaries. */
static void update_summaries(PGconn *conn,
                             int electorate_code,
                             int polling_place_code) {
  int g,c;
  int fp;

  static int previous_electorate_code = -1,
    previous_polling_place_code = -1;

  /* Check if still collecting data for the same
     electorate/polling place */
  if ((electorate_code == previous_electorate_code) &&
      (polling_place_code == previous_polling_place_code))
    return;

  /* Check if this is the first time we've been called */
  if ((previous_electorate_code == -1) &&
      (previous_polling_place_code == -1)) {
    /* Only have to note that we changed code; nothing
       to be stored. */
    previous_electorate_code = electorate_code;
    previous_polling_place_code = polling_place_code;
    CLEAR_FIRST_PREFERENCES;
    return;
  }

  /* Update vote summary table */
  if ( SQL_singleton_int(conn,"SELECT COUNT(*) "
                         "FROM vote_summary "
                         "WHERE electorate_code = %d "
                         "AND polling_place_code = %d;",
                         previous_electorate_code,previous_polling_place_code)
       == 0)
    SQL_command(conn,"INSERT INTO vote_summary "
                "(electorate_code,polling_place_code,"
                "entered_by,entered_at,informal_count) "
                "VALUES (%d,%d,'EVACS scanned','NOW',%u);",
                previous_electorate_code,previous_polling_place_code,
                informal_count);
  else
    SQL_command(conn,"UPDATE vote_summary "
                "SET informal_count = informal_count + %u,"
                "entered_by = 'EVACS scanned',"
                "entered_at = 'NOW' "
                "WHERE electorate_code = %d "
                "AND polling_place_code = %d;",
                informal_count,
                previous_electorate_code,
                previous_polling_place_code);
  /* Must also update reporting data now. */
  reporting_data[previous_electorate_code]->informal_papers +=
    informal_count;
  informal_count = 0;

  /* Update first preference summary table */
  for (g = 0; g < max_num_groups; g++)
    for (c = 0; c < max_num_candidates; c++) {
      fp = FIRST_PREFERENCES(g,c);
      if (fp > 0) {
        if (SQL_singleton_int(conn,"SELECT COUNT(*) "
                              "FROM preference_summary "
                              "WHERE electorate_code = %d "
                              "AND polling_place_code = %d "
                              "AND party_index = %d "
                              "AND candidate_index = %d;",
                              previous_electorate_code,
                              previous_polling_place_code,
                              g,
                              c)
            == 0)
          SQL_command(conn,"INSERT INTO "
                      "preference_summary"
                      "(electorate_code,"
                      "polling_place_code,party_index,"
                      "candidate_index,phoned_primary,"
                      "evacs_primary,final_count) "
                      "VALUES(%d,%d,%d,%d,0,%d,0);",
                      previous_electorate_code,
                      previous_polling_place_code,
                      g,
                      c,
                      fp);
        else
          SQL_command(conn,"UPDATE "
                      "preference_summary "
                      "SET evacs_primary = "
                      "evacs_primary + %d "
                      "WHERE electorate_code = %d "
                      "AND polling_place_code = %d "
                      "AND party_index = %d "
                      "AND candidate_index = %d;",
                      fp,
                      previous_electorate_code,
                      previous_polling_place_code,
                      g,
                      c);
      }
    }
  CLEAR_FIRST_PREFERENCES;

  previous_electorate_code = electorate_code;
  previous_polling_place_code = polling_place_code;
}

static void insert_scanned_vote(PGconn *conn,
                                unsigned int batch_number,
                                unsigned int paper_version,
                                unsigned int electorate_code,
                                char *timestamp,
                                char *preference_list,
                                struct preference preferences[],
                                unsigned int num_preferences,
                                unsigned int polling_place_code, 
                                struct electorate *electorate)
{
  /* Too slow to insert each vote individually. */
  /*
  SQL_command(conn,
              "INSERT INTO %s_confirmed_vote"
              "(batch_number,paper_version,time_stamp,preference_list) "
              "VALUES(%u,%u,'%s','%s');",
              electorate->name,
              batch_number,
              paper_version, 
              timestamp,
              preference_list);
  */

  /* Write the vote to an appropriate temporary file instead. */
  fprintf(vote_files[electorate_code],
          "%u\t%u\t%s\t%s\n",
          batch_number,
          paper_version, 
          timestamp,
          preference_list);

  if (num_preferences != 0)
    FIRST_PREFERENCES(preferences[0].group_index,
                      preferences[0].db_candidate_index)++;
}



/* All votes will be loaded into this PGresult.
   Column 0 = batch number;
   column 1 = paper version,
   column 2 = time stamp,
   column 3 = preference list */
static PGresult *all_votes_to_be_imported;

static int num_of_all_votes_to_be_imported;

static unsigned int import_batch(PGconn *conn_evacs,
                                 unsigned int where_to_start)
{
  unsigned int batch_to_import;
  unsigned int vote_cursor;
  int this_electorate_code;
  struct electorate *this_electorate;
  int this_polling_place_code; 
  /* SIPL 2011: Changed type to conform. */
  /* unsigned char *this_preference_list; */
  char *this_preference_list;
  struct preference preferences_in[PREFNUM_MAX],
    preferences_out[PREFNUM_MAX];
  unsigned int num_preferences_in,num_preferences_out;
  /* SIPL 2011: Changed type to conform. */
  /* unsigned char */
  char
    this_preference_list_normalized[DIGITS_PER_PREF * PREFNUM_MAX + 1];
  int num_rows;
  
  batch_to_import =
    atoi(PQgetvalue(all_votes_to_be_imported,where_to_start,0));
  this_electorate_code = SQL_singleton_int(conn_evacs,
                                           "SELECT electorate_code "
                                           "FROM batch "
                                           "WHERE number = %u;",
                                           batch_to_import);
  if (this_electorate_code < 0) {
    rollback(conn_evacs);
    PQfinish(conn_evacs);
    bailout("\nDatabase error while retrieving details for batch %d\n",
            batch_to_import);
  }
  this_polling_place_code = SQL_singleton_int(conn_evacs,
                                           "SELECT polling_place_code "
                                           "FROM batch "
                                           "WHERE number = %u;",
                                           batch_to_import);
  if (this_polling_place_code < 0) {
    rollback(conn_evacs);
    PQfinish(conn_evacs);
    bailout("\nDatabase error while retrieving polling place "
            "details for batch %d\n",
            batch_to_import);
  }

  /* Call update_summaries here, i.e., before examining the votes,
     because it is used to "flush"
     data from a previous electorate/polling place. */
  update_summaries(conn_evacs,
                   this_electorate_code,this_polling_place_code);


  this_electorate = electorates[this_electorate_code];
  
  vote_cursor = where_to_start;
  
  while ((vote_cursor < num_of_all_votes_to_be_imported) &&
         (atoi(PQgetvalue(all_votes_to_be_imported,vote_cursor,0)) ==
          batch_to_import)) {

    this_preference_list = PQgetvalue(all_votes_to_be_imported,
                                      vote_cursor, 3);
    get_scanned_prefs_for_entry(preferences_in,
                                &num_preferences_in,
                                this_preference_list);
    normalize_scanned_prefs(preferences_out,
                            &num_preferences_out,
                            preferences_in,
                            num_preferences_in);
    pack_scanned_prefs(this_preference_list_normalized,
                       preferences_out,
                       num_preferences_out);
    if (num_preferences_out == 0)
      informal_count++;
    insert_scanned_vote(conn_evacs,
                        batch_to_import,
                        /* paper_version */
                        atoi(PQgetvalue(all_votes_to_be_imported,
                                   vote_cursor, 1)),
                        this_electorate_code,
                        /* timestamp */
                        PQgetvalue(all_votes_to_be_imported,
                                   vote_cursor, 2),
                        this_preference_list_normalized,
                        preferences_out,
                        num_preferences_out,
                        this_polling_place_code, 
                        this_electorate);

    vote_cursor++;
  }

  /* Mark batch as committed */
  num_rows = SQL_command(conn_evacs,"UPDATE batch "
                         "SET committed = true "
                         "WHERE number = %u;",
                         batch_to_import);
  /* Do reporting. */
  reporting_data[this_electorate_code]->batches_imported++;
  reporting_data[this_electorate_code]->papers_imported +=
    (vote_cursor - where_to_start);
  /* Sanity check - check that only one row was updated */
  if ( num_rows != 1 ) {
    rollback(conn_evacs);
    PQfinish(conn_evacs);
    if (num_rows == 0)
      bailout("Batch %u has already been committed!\n",batch_to_import);
    else
      bailout("More than one entry exists for batch %u.\n",batch_to_import);
  }
  return vote_cursor;
}


static void import_all_papers(PGconn *conn_evacs,PGconn *conn_scanned)
{
   int num_batches;
   unsigned int batch_cursor;
   unsigned int vote_cursor;
   /* Progress bar based on 20 5-percent increments;
      displayed only if 20 or more batches  */
   unsigned int next_progress_point=0;
   unsigned int progress_point_increment;
   /* Backspace by 20 spaces, then another 4 for "|100". */
   const char backspace_by_24[] =
     "\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b";

   fprintf(stderr,"  Counting batches . . .\n");

   num_batches = SQL_singleton_int(conn_scanned,
                                   "SELECT COUNT(DISTINCT batch_number) "
                                   "FROM scanned_vote;");
   fprintf(stderr,"  . . . batches counted.\n");

   if (num_batches < 1)
     bailout("Database error while retrieving batches!\n");

   fprintf(stderr,"  Loading papers "
           "from %d batch(es) "
           "into memory . . .\n",num_batches);

   /* Load everything, ordered by batch number.
      It's just too slow to load batches one by one. */
   all_votes_to_be_imported =
     SQL_query(conn_scanned,
               "SELECT batch_number,paper_version,time_stamp,preference_list "
               "FROM scanned_vote "
               "ORDER BY batch_number;");
   fprintf(stderr,"  . . . papers loaded.\n");

   num_of_all_votes_to_be_imported = PQntuples(all_votes_to_be_imported);

   fprintf(stderr,"  Filtering %d paper(s) by electorate "
           "and updating summaries . . .\n",
           num_of_all_votes_to_be_imported);

   /* Compute when to display the next hash.  Division and modulo
      are by 19 (= 20 - 1). */
   progress_point_increment = (num_of_all_votes_to_be_imported - 1) / 19;
   /* Begin progress bar (if there will be one) */
   if (progress_point_increment != 0) {
     next_progress_point = (num_of_all_votes_to_be_imported - 1) % 19;
     fprintf(stderr,"%s", (const char *) "      0|                    |100");
     fprintf(stderr,"%s",backspace_by_24);
     fflush(stderr);
   }

   vote_cursor = 0;
   for (batch_cursor = 0; batch_cursor < num_batches; batch_cursor++) {
     vote_cursor = import_batch(conn_evacs,vote_cursor);

     /* Update progress bar (if there is one) */
     if (progress_point_increment != 0) {
       while (vote_cursor >= next_progress_point) {
         fprintf(stderr, "#");
         fflush(stderr);
         next_progress_point = next_progress_point + progress_point_increment;
       }
     }
   }

   /* Flush the summary for the last electorate/polling place. */
   update_summaries(conn_evacs,-1,-1);

   /* Complete progress bar (if there was one) */
   if (progress_point_increment != 0) {
     fprintf(stderr, "\n");
   }

   PQclear(all_votes_to_be_imported);
   fprintf(stderr,"  . . . all papers filtered.\n");
}



static void bulk_import_papers(PGconn *conn) {
  int i;
  int num_rows;
  /*  fprintf(stderr,"Interrupted . . . cleaning up.\n");*/


  for (i=0; i<=max_electorate; i++) {
    if (electorates[i] && vote_files[i]) {
        fclose(vote_files[i]);
        fprintf(stderr,"  Bulk loading %s votes . . .\n",
                electorates[i]->name);
        num_rows = SQL_command(conn,
                               "COPY %s_confirmed_vote "
                               "(batch_number,paper_version,"
                               "time_stamp,preference_list) "
                               "FROM '%s';",
                               electorates[i]->name,
                               vote_filenames[i]);
        if (num_rows < 0)
          bailout("Error bulk loading %s votes!\n",
                  electorates[i]->name);
        unlink(vote_filenames[i]);
        fprintf(stderr,"    Batches:  %u\n",
                reporting_data[i]->batches_imported);
        fprintf(stderr,"    Papers:   %u\n",
                reporting_data[i]->papers_imported);
        fprintf(stderr,"    Informal: %u\n",
                reporting_data[i]->informal_papers);
        fprintf(stderr,"  . . . %s votes loaded.\n",
                electorates[i]->name);
    }
  }
}


PGconn *conn_evacs;
PGconn *conn_scanned;


static void interruption_handler(int signum)
{
  int i;
  fprintf(stderr,"Interrupted . . . cleaning up.\n");
  if (conn_evacs) {
    rollback(conn_evacs);
    PQfinish(conn_evacs);
  }
  if (conn_scanned)
    PQfinish(conn_scanned);
  for (i=0; i<=max_electorate; i++) {
    if (electorates[i] && vote_files[i]) {
        fclose(vote_files[i]);
        unlink(vote_filenames[i]);
    }
  }
  bailout("Bailing out at user request!\n");
}



bool handle_scanned_votes(void) {
  signal(SIGINT, interruption_handler);
  signal(SIGTERM, interruption_handler);

  fprintf(stderr,"Importing the scanned votes . . .\n");

  conn_evacs=connect_db(DATABASE_NAME);
  conn_scanned=connect_db(LOADDB_NAME);

  setup_electorate_and_ballot_data(conn_evacs);

  /* Start the transaction */
  begin(conn_evacs);

  /* Prevent race condition in SELECT - INSERT or UPDATE code */
  /* This won't block readers - only other writers */
  SQL_command(conn_evacs,"LOCK TABLE vote_summary IN EXCLUSIVE MODE;");
  SQL_command(conn_evacs,"LOCK TABLE preference_summary IN EXCLUSIVE MODE;");

  import_all_papers(conn_evacs,conn_scanned);
  bulk_import_papers(conn_evacs);

  /* End the transaction */
  commit(conn_evacs);
  PQfinish(conn_evacs);
  PQfinish(conn_scanned);

  fprintf(stderr,". . . scanned votes imported.\n");

  return true;
}
