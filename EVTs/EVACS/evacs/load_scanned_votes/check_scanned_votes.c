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

/* Check scanned votes */

/* For isdigit() */
#include <ctype.h>
#include <signal.h>
/* For varargs */
#include <stdarg.h>
/* For malloc() */
#include <stdlib.h>
/* For memset() */
#include <string.h>

#include <common/evacs.h>
#include <common/ballot_contents.h>
#include <common/database.h>
#include <common/get_electorate_ballot_contents.h>
#include "bitset.h"
#include "scanned_votes.h"
#include "check_scanned_votes.h"



/* Highest electorate code */
static int max_electorate=0;

/* These are used as arrays indexed by 1..max_electorate */
static struct electorate **electorates;
static struct ballot_contents **all_ballot_contents;
static int *min_paper_versions,*max_paper_versions;

/* Highest number of groups in any electorate */
static int max_num_groups=0;

/* Highest number of candidates in any group in any electorate */
static int max_num_candidates=0;

/* Bitsets used while examing a preference list; used for checking
   there aren't two preferences marked for the same candidate.
   Use preference_bitsets as an array of bitsets.  To access
   preference_bitsets[g], write:
     (preference_bitsets + (g * preference_bitset_element_size),
   where preference_bitset_element_size has been previously
   assigned the value:
     BITSET_LENGTH_IN_UNITS(max_num_candidates).
   The preference_bitset macro does this for you.
   The total length of the memory allocated for preference_bitsets
   is stored in preference_bitsets_length.
*/
static BITSET_UNIT *preference_bitsets;
unsigned int preference_bitset_element_size;
unsigned int preference_bitsets_length;
#define preference_bitset(g) \
  (preference_bitsets + (g * preference_bitset_element_size))
#define CLEAR_PREFERENCE_BITSETS \
  memset(preference_bitsets,0,preference_bitsets_length)


/* When possible, don't stop after the first error,
   but print a certain number of errors before giving up. */
static int num_errors_found=0;

/* If we find an error, only show this many errors.
   If there are indeed this many errors,
   say that there might be more. */
#define LIMIT_OF_ERRORS_TO_SHOW 10

static void warn_of_possible_further_errors(int num_errors) {
  if (num_errors >= LIMIT_OF_ERRORS_TO_SHOW)
    fprintf(stderr,"(Only %d errors shown.  There might be more.)\n",
            LIMIT_OF_ERRORS_TO_SHOW);
}

/* Call this like bailout(), but it will keep going
   until LIMIT_OF_ERRORS_TO_SHOW is reached. */
static void report_an_error(const char *fmt, ...) {
  va_list arglist;

  num_errors_found++;

  va_start(arglist,fmt);
  vfprintf(stderr,fmt,arglist);
  va_end(arglist);

  warn_of_possible_further_errors(num_errors_found);
  if (num_errors_found >= LIMIT_OF_ERRORS_TO_SHOW)
    bailout("\nBailing out after showing %d errors.\n",
            num_errors_found);
}



static void setup_electorate_and_ballot_data(void) {
  PGconn *conn;
  struct electorate *elec_ptr, *elec_ptr_start;
  struct ballot_contents *ballot_cursor;
  unsigned int i;

  conn=connect_db(DATABASE_NAME);
        
  max_electorate = SQL_singleton_int(conn,"SELECT MAX(code) "
                                      "FROM electorate;");

  if (max_electorate < 0)
    bailout("There are no electorates defined!\n");

  /* Now we can allocate memory for the arrays. Add one in each case
     because we index the arrays starting at one.*/
  electorates = malloc(sizeof(struct electorate *) * (max_electorate + 1));
  if (!electorates)
    bailout("Out of memory while allocating space for electorates!\n");

  min_paper_versions = malloc(sizeof(int) * (max_electorate + 1));
  if (!min_paper_versions)
    bailout("Out of memory while allocating space for "
            "paper version minima!\n");
  max_paper_versions = malloc(sizeof(int) * (max_electorate + 1));
  if (!max_paper_versions)
    bailout("Out of memory while allocating space for "
            "paper version maxima!\n");

  all_ballot_contents = malloc(sizeof(struct ballot_contents *)
                           * (max_electorate + 1));
  if (!all_ballot_contents)
    bailout("Out of memory while allocating space for ballots!\n");

  /* get all electorate data */
  elec_ptr=get_electorates(conn);
  elec_ptr_start = elec_ptr;

  /* convert to arrays for lookups by code */
  for (;elec_ptr;elec_ptr=elec_ptr->next) {
    electorates[elec_ptr->code]=elec_ptr;
    /* Get paper_versions for this electorate */
    min_paper_versions[elec_ptr->code] =
      SQL_singleton_int(conn,"SELECT MIN(rotation_num) "
                        "FROM robson_rotation_%u;",
                        elec_ptr->num_seats);
    max_paper_versions[elec_ptr->code] =
      SQL_singleton_int(conn,"SELECT MAX(rotation_num) "
                        "FROM robson_rotation_%u;",
                        elec_ptr->num_seats);
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
  }
  PQfinish(conn);

  preference_bitset_element_size =
    BITSET_LENGTH_IN_UNITS(max_num_candidates);

  preference_bitsets_length = sizeof(BITSET_UNIT) *
    max_num_groups * preference_bitset_element_size;

  preference_bitsets = malloc(preference_bitsets_length);
}


/* Check all the batch numbers: we know about them, they
   aren't already committed. */
static void check_all_batch_numbers(PGconn *conn) {
  PGresult *result;
  int num_problem_batches;
  int i;

  fprintf(stderr,"  Checking batch numbers used in the data . . .\n");

  /* Check that we already know about all the batch numbers in the data. */
  fprintf(stderr,"    Checking batch numbers are valid . . .\n");
  result = SQL_query(conn,"SELECT DISTINCT batch_number "
                     "FROM scanned_vote "
                     "EXCEPT SELECT DISTINCT number FROM batch "
                     "LIMIT %d;",LIMIT_OF_ERRORS_TO_SHOW);
  num_problem_batches = PQntuples(result);
  if (num_problem_batches < 0)
    bailout("Database query failed!\n");
  if (num_problem_batches > 0) {
    fprintf(stderr,"Invalid batch number(s) in the data:\n");
    for (i=0;i<num_problem_batches;i++)
      fprintf(stderr,"%s\n",PQgetvalue(result,i,0));
    warn_of_possible_further_errors(num_problem_batches);
    bailout("Error with batch numbers.\n");
  }
  PQclear(result);
  fprintf(stderr,"    . . . batch numbers are valid.\n");

  /* Check that there are no batches already committed. */
  fprintf(stderr,"    Checking data contains only "
          "uncommitted batches . . .\n");
  result = SQL_query(conn,"SELECT batch.number FROM "
                     "batch INNER JOIN "
                     "(SELECT DISTINCT batch_number FROM scanned_vote) "
                     "AS sq ON batch.number = sq.batch_number "
                     "WHERE batch.committed = TRUE "
                     "LIMIT %d;",LIMIT_OF_ERRORS_TO_SHOW);
  num_problem_batches = PQntuples(result);
  if (num_problem_batches < 0)
    bailout("Database query failed!\n");
  if (num_problem_batches > 0) {
    fprintf(stderr,"Batch(es) that have already been committed:\n");
    for (i=0;i<num_problem_batches;i++)
      fprintf(stderr,"%s\n",PQgetvalue(result,i,0));
    warn_of_possible_further_errors(num_problem_batches);
    bailout("Error with batch numbers.\n");
  }
  PQclear(result);
  fprintf(stderr,"    . . . there are only uncommitted batches . . .\n");

  fprintf(stderr,"  . . . batch numbers are OK.\n");
}


/* All votes will be loaded into this PGresult.
   Column 0 = batch number; column 1 = paper version,
   column 2 = preference list */
/* The goto statement is used for "error exits" referred
   to in:
   Donald E. Knuth, "Structured Programming with go to Statements",
   Computing Surveys 6 (4): 261-301. 
 */
static PGresult *all_votes_to_be_checked;

static int num_of_all_votes_to_be_checked;

static unsigned int check_batch(PGconn *conn,unsigned int where_to_start)
{
  unsigned int batch_to_check;
  unsigned int vote_cursor;
  int this_electorate_code;
  struct electorate *this_electorate;
  struct ballot_contents *this_ballot;
  /* SIPL 2011: Changed the types to conform to parameter types. */
  /* unsigned char *this_preference_list,*this_preference_list_cursor; */
  char *this_preference_list,*this_preference_list_cursor;
  int this_paper_version;
  unsigned int prefnum,group,candidate;
  
  batch_to_check =
    atoi(PQgetvalue(all_votes_to_be_checked,where_to_start,0));
  this_electorate_code = SQL_singleton_int(conn,
                                           "SELECT electorate_code "
                                           "FROM batch "
                                           "WHERE number = %u;",
                                           batch_to_check);

  if (this_electorate_code < 0)
    /* This can't happen if check_all_batch_numbers() has
       been called first. */
    bailout("\nFound a paper for batch %d that does not exist!\n",
            batch_to_check);

  this_electorate = electorates[this_electorate_code];
  this_ballot = all_ballot_contents[this_electorate_code];

  vote_cursor = where_to_start;
  
  while ((vote_cursor < num_of_all_votes_to_be_checked) &&
         (atoi(PQgetvalue(all_votes_to_be_checked,vote_cursor,0)) ==
          batch_to_check)) {
    /* Check one paper version */
    this_paper_version = atoi(PQgetvalue(all_votes_to_be_checked,
                                         vote_cursor, 1));
    if (this_paper_version < min_paper_versions[this_electorate_code] ||
        this_paper_version > max_paper_versions[this_electorate_code])
      report_an_error("\nIn batch %u, there is a paper with "
                      "paper version %d\n"
                      "but there's "
                      "no such paper version!\n",batch_to_check,
                      this_paper_version);

    /* Check one preference list.  First check it is the
       right length, and contains only digits. */
    this_preference_list = PQgetvalue(all_votes_to_be_checked,
                                      vote_cursor, 2);
    this_preference_list_cursor = this_preference_list;
    while (*this_preference_list_cursor) {
      if (!isdigit(*this_preference_list_cursor)) {
        report_an_error("\nIn batch %u, this preference string has a "
                        "character '%c'\nwhich is not a digit:\n%s\n",
                        batch_to_check,
                        *this_preference_list_cursor,this_preference_list);
        goto end_outer_loop;
      }
      /* SIPL 2011: Changed type to conform. */
      /* this_preference_list_cursor += sizeof(unsigned char); */
      this_preference_list_cursor += sizeof(char);
    }
    if ((this_preference_list_cursor - this_preference_list) %
	/* SIPL 2011: Changed type to conform. */
        /* (DIGITS_PER_PREF * sizeof(unsigned char)) != 0) { */
	(DIGITS_PER_PREF * sizeof(char)) != 0) {
        report_an_error("\nIn batch %u, this preference list has a length "
                        "that is not\na multiple of %d characters:\n%s\n",
                        batch_to_check,
			/* SIPL 2011: Changed type to conform. */
                        /* DIGITS_PER_PREF * sizeof(unsigned char), */
			DIGITS_PER_PREF * sizeof(char),
                        this_preference_list);
        goto end_outer_loop;
    }
    /* Now check the preferences, groups, and candidates */
    CLEAR_PREFERENCE_BITSETS;
    this_preference_list_cursor = this_preference_list;
    while (*this_preference_list_cursor) {
      sscanf(this_preference_list_cursor, (const char *)"%2u%2u%2u",
             &prefnum,&group,&candidate);
      if (prefnum == 0) {
        report_an_error("\nIn batch %u, this preference string has a "
                        "preference numbered 0;\nsuch preferences are "
                        "not permitted:\n%s\n",batch_to_check,
                        this_preference_list);
        goto end_outer_loop;
      }
      if (group >= this_ballot->num_groups) {
        report_an_error("\nIn batch %u, this preference string "
                        "refers to group %u\n"
                        "(counting from 0) but there's "
                        "no such group!\n%s\n",batch_to_check,
                        group,this_preference_list);
        goto end_outer_loop;
      }
      if (candidate >= this_ballot->num_candidates[group]) {
        report_an_error("\nIn batch %u, this preference string refers "
                        "to candidate %u\n"
                        "(counting from 0) in "
                        "group %u (counting from 0)\n"
                        "but there's no such candidate!\n%s\n",
                        batch_to_check,candidate,group,
                        this_preference_list);
        goto end_outer_loop;
      }
      if (BITSET_IS_SET(preference_bitset(group),candidate)) {
        report_an_error("\nIn batch %u, this preference string has two "
                        "different preferences\n"
                        "for the same candidate!\nCandidate %u "
                        "(counting from 0) in "
                        "group %u (counting from 0).\n%s\n",
                        batch_to_check,candidate,group,
                        this_preference_list);
        goto end_outer_loop;
      }
      BITSET_SET_BIT(preference_bitset(group),candidate);
      /* SIPL 2011: Changed type to conform. */
      /* this_preference_list_cursor += DIGITS_PER_PREF*sizeof(unsigned char); */
      this_preference_list_cursor += DIGITS_PER_PREF*sizeof(char);
    }
  end_outer_loop:
    vote_cursor++;
  }
  return vote_cursor;
}


static void check_all_paper_versions_and_preference_lists(PGconn *conn)
{
   int num_batches;
   unsigned int batch_cursor;
   unsigned int vote_cursor;
   /* Progress bar based on 10 10-percent increments;
      displayed only if 10 or more batches  */
   unsigned int next_progress_point=0;
   unsigned int progress_point_increment;
   /* Backspace by 10 spaces, then another 4 for "|100". */
   const char backspace_by_14[] = "\b\b\b\b\b\b\b\b\b\b\b\b\b\b";

   fprintf(stderr,"  Checking all paper versions and "
           "preference lists . . .\n");
   fprintf(stderr,"    Counting batches . . .\n");

   num_batches = SQL_singleton_int(conn,
                                   "SELECT COUNT(DISTINCT batch_number) "
                                   "FROM scanned_vote;");
   fprintf(stderr,"    . . . batches counted.\n");

   if (num_batches < 1)
     bailout("Didn't find any batches to check!\n");

   fprintf(stderr,"    Loading papers "
           "from %d batch(es) "
           "into memory . . .\n",num_batches);

   /* Load everything, ordered by batch number.
      It's just too slow to load batches one by one. */
   all_votes_to_be_checked = SQL_query(conn,
                      "SELECT batch_number,paper_version,preference_list "
                      "FROM scanned_vote "
                      "ORDER BY batch_number;");
   fprintf(stderr,"    . . . papers loaded.\n");

   num_of_all_votes_to_be_checked = PQntuples(all_votes_to_be_checked);

   fprintf(stderr,"    Checking paper versions and preference lists "
           "of %d paper(s) . . .\n",
           num_of_all_votes_to_be_checked);

   /* Compute when to display the next hash.  Division and modulo
      are by 9 (= 10 - 1). */
   progress_point_increment = (num_of_all_votes_to_be_checked - 1) / 9;
   /* Begin progress bar (if there will be one) */
   if (progress_point_increment != 0) {
     next_progress_point = (num_of_all_votes_to_be_checked - 1) % 9;
     fprintf(stderr,"%s", (const char *) "      0|          |100");
     fprintf(stderr,"%s",backspace_by_14);
     fflush(stderr);
   }

   vote_cursor = 0;
   for (batch_cursor = 0; batch_cursor < num_batches; batch_cursor++) {
     vote_cursor = check_batch(conn,vote_cursor);

     /* Update progress bar (if there is one) */
     if (progress_point_increment != 0) {
       while (vote_cursor >= next_progress_point) {
         fprintf(stderr, "#");
         fflush(stderr);
         next_progress_point = next_progress_point + progress_point_increment;
       }
     }
   }
   /* Complete progress bar (if there was one) */
   if (progress_point_increment != 0) {
     fprintf(stderr, "\n");
   }

   PQclear(all_votes_to_be_checked);
   if (num_errors_found == 0) {
     fprintf(stderr,"    . . . all paper versions and "
             "preference lists are OK.\n");
     fprintf(stderr,"  . . . paper version and preference list "
             "checking done.\n");
   }
}


PGconn *conn_scanned;

static void interruption_handler(int signum)
{
  if (conn_scanned)
    PQfinish(conn_scanned);
  bailout("Bailing out at user request!\n");
}


bool check_scanned_votes(void) {

  signal(SIGINT, interruption_handler);
  signal(SIGTERM, interruption_handler);

  fprintf(stderr,"Checking the scanned papers . . .\n");
  setup_electorate_and_ballot_data();

  conn_scanned=connect_db(LOADDB_NAME);

  check_all_batch_numbers(conn_scanned);

  check_all_paper_versions_and_preference_lists(conn_scanned);
  PQfinish(conn_scanned);

  if (num_errors_found > 0)
    bailout(". . . the scanned papers are NOT OK.\n");
  else
    fprintf(stderr,". . . the scanned papers are OK.\n");

  return true;
}
