/*
   This file is (C) copyright 2001-2007 Software Improvements, Pty Ltd
*/

/*
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public license for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include <common/batch.h>
#include <common/database.h>
#include <common/voter_electorate.h>

#include "batch_edit.h"
#include "batch_edit_2.h"

#define TIME_STR_LEN            50
#define LOG_FILE_NAME_STR_LEN  100

// ===================================================================

/*
   The routine get_date_and_time() is used to create a string
   specifying the current date and time in the format:

   <Day of Week> dd mmm yyyy hh:mm:ss

   where: hh is 00 .. 23.
*/
static void get_date_and_time (      char   *time_str,
                               const size_t  str_len) {

  time_t current_time;
  struct tm *ltime;

  time (&current_time);
  ltime = localtime(&current_time);

  strftime(time_str,
           str_len,
           "%A %d %B %Y  %X",
           ltime);
} // get_date_and_time()

// -------------------------------------------------------------------

/*
   The routine open_log_file() is used to create a disk file to which
    debugging information is written.
   The routine redirect information being written to the standard
    error device to the log file.
   The routine writes the name of the file and the file's creation
    date and time to the file.
   Note: Only one debugging log file can be open at a time by a program.
*/
FILE *open_log_file(const char *file_name) {

   extern FILE *stderr;
          FILE *err_file;
          char  time_string[TIME_STR_LEN];
          char  name_of_file[LOG_FILE_NAME_STR_LEN];

   strcpy(name_of_file, LOG_FILE_DIR);
   strcat(name_of_file, file_name);
   strcat(name_of_file, "_");
   strcat(name_of_file, get_operator_id());
   strcat(name_of_file, ".txt");

   err_file = freopen(name_of_file, "w", stderr);
   get_date_and_time(time_string, TIME_STR_LEN);
   fprintf(stderr, "Log file: %s created on %s\n\n",
           name_of_file,
           time_string);
   return err_file;

} // open_log_file()

// -------------------------------------------------------------------

/*
  The routine close_log_file() closes the currently open debugging
   log file.
  Information being written to the standard error device, which was
   being redirected to the debugging log file, is redirected to the
   standard output device; i.e. the terminal.
*/
void close_log_file(void) {

   char  time_string[TIME_STR_LEN];

   get_date_and_time(time_string, TIME_STR_LEN);
   fprintf(stderr, "\nLog file closed at %s\n", time_string);
   fflush(stderr);
   freopen("/dev/tty1", "w", stderr);

} // close_log_file()

// ===================================================================
/*
  The routine get_max_entry_index_of is used to obtain the number of
   entry indexes associated with a specified paper.
*/
unsigned int get_max_entry_index_of (      PGconn       *conn,
                                     const unsigned int  batch_number,
                                     const unsigned int  paper_id,
                                     const char         *electorate_name) {
   unsigned int num_entries;

   fprintf(stderr, "\nEntered get_max_entry_index_of\n");
   fprintf(stderr, "    batch_number .. %u\n", batch_number);
   fprintf(stderr, "    paper_id ...... %u\n", paper_id);
   fprintf(stderr, "    electorate_name '%s'\n", electorate_name);

   fprintf(stderr,
           "\nIssue sql query: "
              "SELECT MAX(e.index) FROM %s_entry e, %s_paper p\n"
              "      WHERE p.batch_number = %u "
              "AND e.paper_id = p.id AND p.id = %u;\n",
           electorate_name, electorate_name,
           batch_number,    paper_id);

   num_entries = (unsigned int) SQL_singleton_int(conn,
                                                  "SELECT MAX(e.index) "
                                                  "FROM %s_entry e,%s_paper p "
                                                  "WHERE p.batch_number = %u "
                                                  "AND e.paper_id = p.id "
                                                  "AND p.id = %u; ",
                                                  electorate_name,
                                                  electorate_name,
                                                  batch_number,
                                                  paper_id);

   fprintf(stderr, "Leaving get_max_entry_index_of: returning %d\n",
                   num_entries);
   return num_entries;
}
// ===================================================================
/*
   The routine create_empty_paper() creates an entry into the paper
    table for an electorate (e.g. brindabella_paper).
   It does not create an associated entry in an entry table (e.g.
    brindabella_entry) listing preferences.
*/
static unsigned int create_empty_paper(      PGconn       *conn,
                                       const unsigned int  paper_index,
                                       const unsigned int  batch_number,
                                       const char         *electorate_name) {
   int   paper_id;
   char *paper_seq_name;

   fprintf(stderr, "\nEntered create_empty_paper\n");
   fprintf(stderr, "   paper_index ... %u\n", paper_index);
   fprintf(stderr, "   batch_number .. %u\n", batch_number);
   fprintf(stderr, "   electorate_name '%s'\n", electorate_name);

   fprintf(stderr,
           "\nIssue sql command: "
              "INSERT INTO %s_paper (batch_number, index)\n"
              "                   VALUES(%u, %u);\n",
           electorate_name,
           batch_number,
           paper_index);

   SQL_command(conn,
               "INSERT INTO %s_paper (batch_number, index) VALUES(%u, %u);\n",
               electorate_name,
               batch_number,
               paper_index);

   /* retrieve the serial id of the INSERTed paper */
   paper_seq_name = sprintf_malloc("%s_paper_id_seq",
                                   electorate_name);
   paper_id       = get_seq_currval(conn, paper_seq_name);
   free (paper_seq_name);

   fprintf(stderr,
           "Leaving create_empty_paper: paper_id = %u\n",
           paper_id);
   return (unsigned int) paper_id;

} // create_empty_paper()


// ===================================================================
/*
  The routine null_entry_id() is used to set one of the active entries (i.e.
   entry_id1 or entry_id2 in the entry table for an electorate (e.g
   brindabella_entry) for a specified paper to '-1'.
  This is done for the case where a paper is deleted and there are no longer
   two active entries for a specified paper.
  If this is not done, then at a later time via either inserting or appending
   a paper to an active entry index, there again becomes two active entries
   for a paper, then the new active entry index will use entry_id2 by default
   when it should have used entry_id1. Setting the specified entry_id(1|2) to
   '-1' will result in the correct entry_id being used at a later time.
*/
static void null_entry_id(      PGconn       *conn,
                          const unsigned int  paper_id,
                          const unsigned int  paper_index,
                          const unsigned int  entry_index,
                          const unsigned int  batch_number,
                          const char         *electorate_name) {

   int   temp;
   int   num_rows_updated;
   int   active_entry1;
   int   active_entry2;
   char *entry_field_name;

   fprintf(stderr, "\nEntered null_entry_id\n");
   fprintf(stderr, "   paper_id ...... %d\n", paper_id);
   fprintf(stderr, "   paper_index ... %d\n", paper_index);
   fprintf(stderr, "   entry_index ... %u\n", entry_index);
   fprintf(stderr, "   batch_number .. %u\n", batch_number);
   fprintf(stderr, "   electorate_name '%s'\n", electorate_name);

   get_active_entries (conn,
                       electorate_name,
                       batch_number,
                       paper_index,
                       &active_entry1,
                       &active_entry2);
   fprintf(stderr, "\nactive_entry1 is %d\n", active_entry1);
   fprintf(stderr, "active_entry2 is %d\n", active_entry2);

   temp = 0;
   if      (active_entry1 == entry_index) temp = 1;
   else if (active_entry2 == entry_index) temp = 2;

   if (temp == 0) {
      fprintf(stderr, "Did not find a match for an active entry.\n");
   } else {
        entry_field_name = sprintf_malloc("entry_id%u", temp);
        fprintf(stderr,
                "\nIssue sql command: "
                   "UPDATE %s_paper SET %s = -1 WHERE id = %u;\n",
                electorate_name,
                entry_field_name,
                paper_id);

        num_rows_updated = SQL_command(conn,
                                       "UPDATE %s_paper SET %s = -1 "
                                          "WHERE id = %u;",
                                       electorate_name,
                                       entry_field_name,
                                       paper_id);
        fprintf(stderr, "num_rows_updated is %u\n", num_rows_updated);
     }
   fprintf(stderr, "Leaving null_entry_id\n");
} // null_entry_id()

// -------------------------------------------------------------------
/*
  The routine insert_entry_into_db() is used to write information
   (e.g. operator id, number of preferences, the preference list, etc.)
   to the entry table for an electorate (e.g. brindabella_entry) for
   a specified entry_index.
  The Supervisor's tick for the associated entry in the paper table is
   set to false.
*/
static void insert_entry_into_db(      PGconn       *conn,
                                 const int           paper_id,
                                 const unsigned int  to_entry_index,
                                 const unsigned int  paper_version,
                                 const unsigned int  num_preferences,
                                 const unsigned int  batch_number,
                                 const char         *operator_id,
                                 const char         *electorate_name,
                                 const char         *preference_list) {

   unsigned int num_entries;

   fprintf(stderr, "\nEntered insert_entry_into_db\n");
   fprintf(stderr, "    paper_id ...... %u\n", paper_id);
   fprintf(stderr, "    to_entry_index  %u\n", to_entry_index);
   fprintf(stderr, "    paper_version . %u\n", paper_version);
   fprintf(stderr, "    num_preferences %u\n", num_preferences);
   fprintf(stderr, "    batch_number .. %u\n", batch_number);
   fprintf(stderr, "    operator_id ... '%s'\n", operator_id);
   fprintf(stderr, "    electorate_name '%s'\n", electorate_name);
   fprintf(stderr, "    preference_list '%s'\n", preference_list);

   fprintf(stderr,
           "\nIssue sql query: "
              "SELECT MAX(e.index) FROM %s_entry e, %s_paper p\n"
              "      WHERE p.batch_number = %u "
              "AND e.paper_id = p.id AND p.id = %u;\n",
           electorate_name, electorate_name,
           batch_number,    paper_id);

   num_entries = (unsigned int) SQL_singleton_int(conn,
                                                  "SELECT MAX(e.index) "
                                                  "FROM %s_entry e,%s_paper p "
                                                  "WHERE p.batch_number = %u "
                                                  "AND e.paper_id = p.id "
                                                  "AND p.id = %u; ",
                                                  electorate_name,
                                                  electorate_name,
                                                  batch_number,
                                                  paper_id);

   fprintf(stderr, "num_entries is %d\n", num_entries);

   fprintf(stderr,
           "\nIssue sql command: "
              "INSERT INTO %s_entry (index, operator_id, paper_id, "
              "paper_version, num_preferences, preference_list)\n"
              "         VALUES(%d, '%s', %d, %u, %u, '%s');\n",
           electorate_name,
           to_entry_index,  operator_id,
           paper_id,        paper_version,
           num_preferences, preference_list);

   SQL_command(conn,
               "INSERT INTO %s_entry (index, operator_id, paper_id, "
                  "paper_version, num_preferences, preference_list) "
                  "VALUES(%d, '%s', %d, %u, %u, '%s');",
               electorate_name,
               to_entry_index,  operator_id,     paper_id,
               paper_version,   num_preferences, preference_list);

   fprintf(stderr,
           "\nIssue sql command: "
              "UPDATE %s_paper SET supervisor_tick = false "
              "WHERE id = %d;\n",
           electorate_name,
           paper_id);

   SQL_command(conn,
               "UPDATE %s_paper "
                  "SET supervisor_tick = false "
                  "WHERE id = %d;",
               electorate_name,
               paper_id);

   fprintf(stderr, "Leaving insert_entry_into_db\n");

} // insert_entry_into_db()

// ===================================================================

/*
  The routine copy_entry_across() is used to make a copy of a paper's
   information in the entry table for an electorate (e.g. brindabella_entry).
  The copy will be identical, but have a different entry index.
  If the input parameter from_entry_id is positive then information is
   obtained from the entry table where table field id = from_entry_id.
  If the input parameter from_entry_id is negative, then the parameter
   specifies a entry_index * -1. This value, along with the input
   parameter paper_id, is used to obtain preference information from
   the entry_table.
*/

static void copy_entry_across(      PGconn       *conn,
                              const          int  from_entry_id,
                                             int  paper_id,
                              const unsigned int  to_entry_index,
                              const unsigned int  batch_number,
                              const char         *operator_id,
                              const char         *electorate_name) {

   PGresult     *result_prefs       = (PGresult *){NULL};
   unsigned int  from_paper_version;
   unsigned int  num_preferences;
   char         *preference_list    = NULL;

   fprintf(stderr, "\nEntered copy_entry_across\n");
   fprintf(stderr, "    from_entry_id .. %d\n", from_entry_id);
   fprintf(stderr, "    paper_id ....... %d\n", paper_id);
   fprintf(stderr, "    to_entry_index . %u\n", to_entry_index);
   fprintf(stderr, "    batch_number ... %u\n", batch_number);
   fprintf(stderr, "    operator_id .... '%s'\n", operator_id);
   fprintf(stderr, "    electorate_name  '%s'\n", electorate_name);

   if (paper_id <= 0) {
      // As we are copying across, the paper_id value must be valid

      fprintf(stderr,
              "ERROR: (copy_entry_across) Invalid value for "
                 "'paper_id(%d)'. Should be > 0.\n",
              paper_id);
   }

   if (from_entry_id < 0) {
      // If the entry_id is negative, then it is actually the
      //  to_entry_index * -1.

      fprintf(stderr,
              "\nIssue sql query: SELECT paper_version, num_preferences, "
                 "preference_list\n"
                 "      FROM %s_entry WHERE paper_id = %u AND index = %d;\n",
              electorate_name,
              paper_id,
              (-1 * from_entry_id));

      result_prefs = SQL_query (conn,
                                "SELECT paper_version, num_preferences, "
                                  "preference_list "
                                  "FROM %s_entry "
                                  "WHERE paper_id = %u AND index = %d;",
                                electorate_name,
                                paper_id,
                               ( -1*from_entry_id));

   } else {
        fprintf(stderr,
                "\nIssue sql query: "
                   "SELECT paper_version, num_preferences, preference_list "
                   " FROM  %s_entry WHERE id = %u;\n",
                electorate_name,
                from_entry_id);

        result_prefs = SQL_query(conn,
                                 "SELECT paper_version, num_preferences, "
                                        "preference_list "
                                    "FROM  %s_entry WHERE id = %u;",
                                 electorate_name,
                                 from_entry_id);
   }

   if (PQntuples(result_prefs) < 1) {
      fprintf(stderr,
              "ERROR: No entries with from_entry_id(%u) - bailout.\n",
              from_entry_id);

      bailout("ERROR: No entries with id(%u)\n", from_entry_id);
   }

   fprintf(stderr,
           "%u entries were found for 'from_entry_id(%d)'.\n",
           PQntuples(result_prefs),
           from_entry_id);

   from_paper_version = atoi(PQgetvalue(result_prefs, 0, 0));
   num_preferences    = atoi(PQgetvalue(result_prefs, 0, 1));
   preference_list    =      PQgetvalue(result_prefs, 0, 2);

   fprintf(stderr, "from_paper_version %u\n", from_paper_version);
   fprintf(stderr, "num_preferences .. %u\n", num_preferences);
   fprintf(stderr, "preference_list .. '%s'\n", preference_list);

   insert_entry_into_db (conn,
                         paper_id,
                         to_entry_index,
                         from_paper_version,
                         num_preferences,
                         batch_number,
                         operator_id,
                         electorate_name,
                         preference_list);

   PQclear(result_prefs);

   fprintf(stderr, "Leaving copy_entry_across\n");

} //copy_entry_across()

// -------------------------------------------------------------------
/*
   The routine copy_entry_down() is used to copy a paper's entry from
    one entry index to another, where the paper index of the new entry
    is one below the entry from where it was copied.
*/
static void copy_entry_down(      PGconn       *conn,
                            const unsigned int  from_entry_id,
                            const          int  from_paper_index,
                            const unsigned int  new_entry_index,
                            const unsigned int  batch_number,
                            const char         *operator_id,
                            const char         *electorate_name) {

   PGresult     *result_prefs       = (PGresult *){NULL};
   unsigned int  from_paper_version;
   unsigned int  num_preferences;
            int  to_paper_id;
   char         *preference_list    = NULL;

   fprintf(stderr, "\nEntered copy_entry_down\n");
   fprintf(stderr, "    from_entry_id .. %u\n", from_entry_id);
   fprintf(stderr, "    from_paper_index %d\n", from_paper_index);
   fprintf(stderr, "    new_entry_index  %u\n", new_entry_index);
   fprintf(stderr, "    batch_number ... %u\n", batch_number);
   fprintf(stderr, "    operator_id .... '%s'\n", operator_id);
   fprintf(stderr, "    electorate_name  '%s'\n", electorate_name);

   if (from_entry_id <= 0) {
      fprintf(stderr,
              "ERROR: (copy_entry_across) Invalid value for "
                 "'form_entry_id (%d)'. Should be > 0\n",
              from_entry_id);
      bailout("ERROR: Invalid value for entry id(%d)\n", from_entry_id);
   }

   fprintf(stderr,
           "\nIssue sql query: SELECT paper_version, num_preferences, "
              "preference_list FROM %s_entry WHERE id = %u;\n",
           electorate_name,
           from_entry_id);

   result_prefs = SQL_query(conn,
                            "SELECT paper_version, num_preferences, "
                                   "preference_list "
                               "FROM  %s_entry "
                               "WHERE id = %u;",
                            electorate_name,
                            from_entry_id);

   if (PQntuples(result_prefs) < 1) {
      fprintf(stderr,
              "ERROR: No entries with from_entry_id(%d) - bailout.\n",
              from_entry_id);

      bailout("ERROR: No entries with id(%d)\n", from_entry_id);
   }

   fprintf(stderr,
           "%u entries were found for 'from_entry_id(%u)'.\n",
           PQntuples(result_prefs),
           from_entry_id);

   from_paper_version = atoi(PQgetvalue(result_prefs, 0, 0));
   num_preferences    = atoi(PQgetvalue(result_prefs, 0, 1));
   preference_list    =      PQgetvalue(result_prefs, 0, 2);

   fprintf(stderr, "from_paper_version %u\n", from_paper_version);
   fprintf(stderr, "num_preferences .. %u\n", num_preferences);
   fprintf(stderr, "preference_list .. '%s'\n", preference_list);

   fprintf(stderr,
           "\nIssue sql query: SELECT id FROM %s_paper "
              "WHERE batch_number = %u AND index = %d;\n",
           electorate_name,
           batch_number,
           from_paper_index);

   to_paper_id = SQL_singleton_int(conn,
                                   "SELECT id "
                                      "FROM %s_paper "
                                      "WHERE batch_number = %u AND index = %d;",
                                   electorate_name,
                                   batch_number,
                                   from_paper_index - 1);

   fprintf(stderr, "to_paper_id is %d\n", to_paper_id);
   assert (to_paper_id > 0);

   insert_entry_into_db (conn,
                         to_paper_id,
                         new_entry_index,
                         from_paper_version,
                         num_preferences,
                         batch_number,
                         operator_id,
                         electorate_name,
                         preference_list);

   if (result_prefs)
      PQclear(result_prefs);
   else
      free(preference_list);

   fprintf(stderr, "Leaving copy_entry_down\n");

} //copy_entry_down()

// -------------------------------------------------------------------
/*
   The routine copy_entry_up() is used to copy a paper's entry from
    one entry index to another, where the paper index of the new entry
    is one above the entry from where it was copied.
   If there isn't an entry in the associated paper table for the
    new entry table, then a new paper table entry will be created.
*/
static void copy_entry_up(      PGconn       *conn,
                          const unsigned int  from_entry_id,
                          const          int  from_paper_index,
                          const unsigned int  new_entry_index,
                          const unsigned int  batch_number,
                          const char         *operator_id,
                          const char         *electorate_name) {

   PGresult     *result_prefs       = (PGresult *){NULL};
   unsigned int  from_paper_version;
   unsigned int  num_preferences;
            int  to_paper_id;
   char         *preference_list    = NULL;

   fprintf(stderr, "\nEntered copy_entry_up (CPUp)\n");
   fprintf(stderr, "    from_entry_id .. %u\n", from_entry_id);
   fprintf(stderr, "    from_paper_index %d\n", from_paper_index);
   fprintf(stderr, "    new_entry_index  %u\n", new_entry_index);
   fprintf(stderr, "    batch_number ... %u\n", batch_number);
   fprintf(stderr, "    operator_id .... '%s'\n", operator_id);
   fprintf(stderr, "    electorate_name  '%s'\n", electorate_name);

   if (from_entry_id <= 0) {
      fprintf(stderr,
              "ERROR: (copy_entry_up) Invalid value for "
                 "'form_entry_id (%d)'. Should be > 0.\n",
              from_entry_id);
      bailout("ERROR: Invalid value for entry id(%d)\n", from_entry_id);
   }

   fprintf(stderr,
           "\nCPUp: Issue sql query: SELECT paper_version, num_preferences, "
              "preference_list FROM %s_entry WHERE id = %u;\n",
           electorate_name,
           from_entry_id);

   result_prefs = SQL_query(conn,
                            "SELECT paper_version, num_preferences, "
                                   "preference_list "
                               "FROM  %s_entry WHERE id = %u;",
                            electorate_name,
                            from_entry_id);

   if (PQntuples(result_prefs) < 1) {
      fprintf(stderr,
              "CPUp: ERROR: No entries with from_entry_id(%u) - bailout.\n",
              from_entry_id);

      bailout("ERROR: No entries with id(%u)\n", from_entry_id);
   }

   fprintf(stderr,
           "CPUp: %u entries were found for 'from_entry_id(%u)'.\n",
           PQntuples(result_prefs),
           from_entry_id);

   from_paper_version = atoi(PQgetvalue(result_prefs, 0, 0));
   num_preferences    = atoi(PQgetvalue(result_prefs, 0, 1));
   preference_list    =      PQgetvalue(result_prefs, 0, 2);

   fprintf(stderr, "CPUp: from_paper_version %u\n", from_paper_version);
   fprintf(stderr, "CPUp: num_preferences .. %u\n", num_preferences);
   fprintf(stderr, "CPUp: preference_list .. '%s'\n", preference_list);

   fprintf(stderr,
           "\nCPUp: Issue sql query: SELECT id FROM %s_paper "
              "WHERE batch_number = %u AND index = %d;\n",
           electorate_name,
           batch_number,
           from_paper_index + 1);

   to_paper_id = SQL_singleton_int(conn,
                                   "SELECT id "
                                      "FROM %s_paper "
                                      "WHERE batch_number = %u "
                                      "AND index = %d;",
                                   electorate_name,
                                   batch_number,
                                   from_paper_index + 1);

   fprintf(stderr, "CPUp: to_paper_id is %d\n", to_paper_id);
   if (to_paper_id <= 0) {
      to_paper_id = create_empty_paper(conn,
                                       from_paper_index + 1,
                                       batch_number,
                                       electorate_name);
   }

   insert_entry_into_db (conn,
                         to_paper_id,
                         new_entry_index,
                         from_paper_version,
                         num_preferences,
                         batch_number,
                         operator_id,
                         electorate_name,
                         preference_list);

   PQclear(result_prefs);

   fprintf(stderr, "CPUp: Leaving copy_entry_up\n");

} //copy_entry_up()

// ===================================================================
/*
  The routine get_other_entry_id() takes an entry_index, and (assuming
   it is an active entry) determines the id of the other active entry.
  This is used when either inserting a paper or appending a paper.
  When these actions are performed, the information from the entry table
   for an electorate is copied from the other active entry if the
   information exists.
  The information may need to be modified/edited by a Supervisor.
*/
static int get_other_entry_id (      PGconn       *conn,
                               const          int  paper_index,
                               const unsigned int  entry_index,
                               const unsigned int  batch_number,
                               const char         *electorate_name) {
   int return_value;
   int active_entry1;
   int active_entry2;

   fprintf(stderr, "\nEntered get_other_entry_id\n");
   fprintf(stderr, "   paper_index ... %d\n", paper_index);
   fprintf(stderr, "   entry_index ... %u\n", entry_index);
   fprintf(stderr, "   batch_number .. %u\n", batch_number);
   fprintf(stderr, "   electorate_name '%s'\n", electorate_name);

   get_active_entries (conn,
                       electorate_name,
                       batch_number,
                       paper_index,
                       &active_entry1,
                       &active_entry2);

   if ((active_entry1 == -1) && (active_entry2 == -1))
      return 0;
   else if (active_entry1 == -1) return_value = active_entry2;
   else if (active_entry2 == -1) return_value = active_entry1;
   else if (entry_index == active_entry1) return_value = active_entry2;
   else                                   return_value = active_entry1;

   fprintf(stderr, "active_entry1 is %d\n", active_entry1);
   fprintf(stderr, "active_entry2 is %d\n", active_entry2);
   fprintf(stderr,
           "Leaving get_other_value - return_value is %d\n",
           return_value);
   return return_value;
} // get_other_entry_id

// -------------------------------------------------------------------
/*
  The routine update_entry() is used to direct the setting the entry_id1
   or entry_id2 field for a paper's entry in the paper table of an
   electorate (e.g. brindabella_paper).
  This routine is responsible for determining whether entry_id1 or
   entry_id2 is to be used.
  This is based on the existing values for entry_id1 and entry_id2 fields,
   and it is assumed that the one of the fields specifies the entry
   index from where entry table information was being copied.
  If the copying, resulting from an insertion, deletion, or appending,
   is NOT from an active entry, then entry_id2 is most likely to be
   used (possible not what the Supervisor doing the work wants).
*/
static void update_entry(      PGconn       *conn,
                         const          int  paper_index,
                         const unsigned int  old_entry_index,
                         const unsigned int  new_entry_index,
                         const unsigned int  batch_number,
                         const char         *electorate_name) {

   int  active_entry1;
   int  active_entry2;
   int  entry_id;

   fprintf(stderr, "\nEntered update_entries\n");
   fprintf(stderr, "   paper_index ... %d\n", paper_index);
   fprintf(stderr, "   old_entry_index %d\n", old_entry_index);
   fprintf(stderr, "   new_entry_index %u\n", new_entry_index);
   fprintf(stderr, "   batch_number .. %u\n", batch_number);
   fprintf(stderr, "   electorate_name '%s'\n", electorate_name);

   get_active_entries (conn,
                       electorate_name,
                       batch_number,
                       paper_index,
                       &active_entry1,
                       &active_entry2);

   fprintf(stderr, "active_entry1 is %d\n", active_entry1);
   fprintf(stderr, "active_entry2 is %d\n", active_entry2);

   /* if the entry index from where the information is being
      copied/modified is an active entry, then the same entry
      index is to be used for the new entry. Setting the variable
      entry_id to a negative number directs the routine
      update_active_entries (common/batch.c) to use the absolute
      value of specified entry id.
   */

   if      (old_entry_index == active_entry1) entry_id = -1;
   else if (old_entry_index == active_entry2) entry_id = -2;
        else if ((active_entry1 == -1) || (active_entry2 == -1)) {
                fprintf(stderr,
                        "active_entry1 || active_entry2 == -1, "
                           "get values for paper_index = 1\n");
                get_active_entries (conn,
                                    electorate_name,
                                    batch_number,
                                    1,  // paper_index
                                    &active_entry1,
                                    &active_entry2);

                fprintf(stderr, "active_entry1 is %d\n", active_entry1);
                fprintf(stderr, "active_entry2 is %d\n", active_entry2);

                /* This time we need to check against the new entry index */

                if      (new_entry_index == active_entry1) entry_id = -1;
                else if (new_entry_index == active_entry2) entry_id = -2;
                     else                                  entry_id =  2;
            } else entry_id = 2;

   fprintf(stderr, "entry_id is %d\n", entry_id);

   update_active_entries (conn,
                          batch_number,
                          paper_index,
                          entry_id,
                          electorate_name);
   fprintf(stderr, "Leaving update_entry\n");

} // update_entry()

// ===================================================================
/*
  The routing get_new_entry_index() is used to determine the entry index
   to which information is to be copied as part of an insertion, deletion,
   or appending.
  The new entry is the highest entry index that currently exists for a
   batch plus one.
*/
static unsigned int get_new_entry_index(      PGconn   *conn,
                                              PGresult *result,
                                        const int       num_rows,
                                        const char     *electorate_name) {
   unsigned int i;
   unsigned int paper_id;
   int          entry_index = -1;
   int          temp;

   fprintf(stderr, "\nEntered get_new_entry_index\n");
   fprintf(stderr, "    num_rows ...... %d\n", num_rows);
   fprintf(stderr, "    electorate_name '%s'\n\n", electorate_name);

   for (i = 0; i < num_rows; i++) {
      paper_id = atoi(PQgetvalue(result, i, 1));
      //fprintf(stderr, "paper_id is %u\n", paper_id);
      fprintf(stderr,
              "\nIssue sql query: SELECT MAX(index) FROM %s_entry "
                 "WHERE paper_id = %d;\n",
              electorate_name,
              paper_id);

      temp = SQL_singleton_int(conn,
                               "SELECT MAX(index) "
                                 "FROM %s_entry "
                                 "WHERE paper_id = %d;",
                               electorate_name,
                               paper_id);

      if (temp > entry_index) entry_index = temp;
   }

   if (temp < 0) temp = 0;

   entry_index++;
   fprintf(stderr,
           "Leaving get_new_entry_num - new entry is %d\n",
           entry_index);

   return (unsigned int) entry_index;

} // get_new_entry_index()

// ===================================================================
/*
  The routine delete_paper() is used to perform the actions associated
   with deleting a paper from a specified entry index:
   - request necessary information from the paper and entry tables for
      the electorate for a specified entry index and batch.
   - reject deletion request if the paper to be deleted is the last
      paper for the entry index and the number of papers is less than or
      equal to the batch size.
   - call get_new_entry_index()
   - for each paper returned via the database request do
   -   if paper index is less than the paper being deleted then
   -      call copy_entry_across()
   -      call update_entry()
   -   if paper index equals the paper to be deleted, then
   -      do nothing
   -   if the paper index is greater than the paper to be deleted, then
   -      call copy_entry_down()
   -      call update_entry()
*/

static void delete_paper(      PGconn       *conn,
                         const unsigned int  batch_number,
                         const unsigned int  paper_to_delete,
                         const unsigned int  entry_index,
                         const char         *operator_id) {

   PGresult     *result;
   unsigned int  db_query_entry_id;
   unsigned int  i;
   unsigned int  new_entry_index;
   int           batch_size;
   int           db_query_paper_id;
   int           db_query_paper_index;
   int           num_papers;
   int           num_rows;
   char         *electorate_name = (char *) get_voter_electorate()->name;
   char         *db_query_operator_id;
   bool          copy_down = false;

   fprintf(stderr, "\nEntered delete_paper\n");
   fprintf(stderr, "    batch_number .. %u\n", batch_number);
   fprintf(stderr, "    paper_to_delete %u\n", paper_to_delete);
   fprintf(stderr, "    entry_index ... %u\n", entry_index);
   fprintf(stderr, "    operator_id ... '%s'\n", operator_id);
   fprintf(stderr, "    electorate_name '%s'\n", electorate_name);

   /* retrieve all entries posessing an <entry_index> of each paper */

   fprintf(stderr,
           "\nIssue sql query: SELECT p.index, p.id, e.id, e.operator_id "
              "FROM %s_paper p, %s_entry e\n"
              "    WHERE p.batch_number = %u AND e.paper_id = p.id "
              "AND e.index = %u;\n",
           electorate_name,
           electorate_name,
           batch_number,
           entry_index);

   result = SQL_query(conn,
                      "SELECT p.index, p.id, e.id, e.operator_id "
                        "FROM   %s_paper p, %s_entry e "
                        "WHERE  p.batch_number = %u "
                        "AND    e.paper_id     = p.id "
                        "AND    e.index        = %u;",
                      electorate_name,
                      electorate_name,
                      batch_number,
                      entry_index);

   num_rows = PQntuples(result);
   fprintf(stderr, "num_rows %d of data found\n", num_rows);

   begin(conn);

   /* Don't want to see other session's updates while in transaction */
   fprintf(stderr,
           "\nIssue sql command: "
           "'SET TRANSACTION ISOLATION LEVEL SERIALIZABLE;'\n");

   SQL_command(conn, "SET TRANSACTION ISOLATION LEVEL SERIALIZABLE;");

   /* record delete details */
   log_batch_operation(conn, batch_number, (enum batch_op) DELETE,
                       (int) paper_to_delete, (int) entry_index);

   /* declared batch size */
   batch_size = get_batch_size(conn, batch_number);
   fprintf(stderr, "batch_size is %d\n", batch_size);

   /* actual batch_size */
   fprintf(stderr,
           "\nIssue sql query: SELECT count(*) from %s_paper "
             "WHERE batch_number = %u;\n",
           electorate_name,
           batch_number);

   num_papers = SQL_singleton_int(conn,
                                  "SELECT count(*) from %s_paper "
                                     "WHERE batch_number = %u;",
                                  electorate_name,
                                  batch_number);
   fprintf(stderr, "num_papers is %d\n", num_papers);

   /* Don't delete the paper if is the last or is ignored */
   if (! (paper_to_delete == num_papers && num_papers > batch_size)) {

      fprintf(stderr, "Start processing the papers\n");

      new_entry_index = get_new_entry_index(conn,
                                            result,
                                            num_rows,
                                            electorate_name);
      for (i = 0; i < num_rows; i++) {
         db_query_paper_index = atoi(PQgetvalue(result, i, 0));
         db_query_paper_id    = atoi(PQgetvalue(result, i, 1));
         db_query_entry_id    = atoi(PQgetvalue(result, i, 2));
         db_query_operator_id =      PQgetvalue(result, i, 3);

         fprintf(stderr, "\n*************************************************");
         fprintf(stderr, "db row = %u\n", i);
         fprintf(stderr, "   db_query_paper_index %d\n", db_query_paper_index);
         fprintf(stderr, "   db_query_paper_id .. %d\n", db_query_paper_id);
         fprintf(stderr, "   db_query_entry_id .. %u\n", db_query_entry_id);
         fprintf(stderr, "   db_query_operator_id '%s'\n", db_query_operator_id);

         if ((!copy_down) && (db_query_paper_index == paper_to_delete)) {
           copy_down = true;

         } else
              if (copy_down) {
                 copy_entry_down (conn,
                                  db_query_entry_id,
                                  db_query_paper_index,
                                  new_entry_index,
                                  batch_number,
                                  db_query_operator_id,
                                  electorate_name);
                 update_entry(conn,
                              db_query_paper_index - 1,
                              entry_index,
                              new_entry_index,
                              batch_number,
                              electorate_name);

                 if (i == (num_rows -1)) {
                    /* If the last entry to be moved down from 'old_entry_index'
                       was an active entry, then make it inactive.
                    */
                    null_entry_id(conn,
                                  db_query_paper_id,
                                  db_query_paper_index,
                                  entry_index,
                                  batch_number,
                                  electorate_name);
                 }
              } else {
                   copy_entry_across(conn,
                                     db_query_entry_id,
                                     db_query_paper_id,
                                     new_entry_index,
                                     batch_number,
                                     db_query_operator_id,
                                     electorate_name);
                   update_entry(conn,
                                db_query_paper_index,
                                entry_index,
                                new_entry_index,
                                batch_number,
                                electorate_name);
                }

      } //end for each paper entry from database
   } else {
        fprintf(stderr, "ERROR: An attempt to delete the last entry.\n");
        }

   /* now delete the all entries of last paper if index > batch size */

   remove_paper(conn,
                electorate_name,
                batch_number,
                paper_to_delete);

   PQclear(result);
   commit(conn);
   fprintf(stderr, "Leaving delete_paper\n");

} // delete_paper()

// -------------------------------------------------------------------
/*
  The routine delete_duplicate_paper() is used to collect initial
   information and to decide whether the deletion of a paper is to
   precede.
  The following actions are performed:
  - get the batch size
  - get the number of papers in the batch
  - get index of paper to be deleted
  - if the index of the paper to be deleted equals the number of papers
     in the batch, and the number of papers is less than the batch size, then
  -    reject the deletion request.
  - get the entry index from which the paper is to be deleted
  - if the entry index is invalid, then
  -    reject the deletion request
  - if the deletion request is to proceed, then
  -    call delete_paper()
*/
void delete_duplicate_paper(      PGconn       *conn,
                            const unsigned int  batch_number,
                            const unsigned int  electorate_code)
{
         unsigned int  entry_index;
         int           batch_size;
         int           num_papers;
	 /* SIPL 2011: Changed types of paper_id and paper_index
	    to conform to parameter types.*/
         /* int           paper_id; */
         /* int           paper_index; */
         unsigned int           paper_id;
         unsigned int           paper_index;
         char          operator_id[OPERATOR_ID_LEN + 1];

   const char         *electorate_name = (char*) get_voter_electorate()->name;

   fprintf(stderr, "\nEntered delete_diplicate_paper\n"
                     "==============================\n");
   fprintf(stderr, "    batch_number .. %u\n", batch_number);
   fprintf(stderr, "    electorate_code %u\n", electorate_code);
   fprintf(stderr, "    electorate_name '%s'\n", electorate_name);

   /* declared batch size */
   batch_size = get_batch_size(conn, batch_number);
   fprintf(stderr, "batch_size is %u\n", batch_size);

   /* actual batch_size */
   fprintf(stderr,
           "\nIssue sql query: SELECT count(*) from %s_paper "
              "WHERE batch_number = %u;\n",
           electorate_name,
           batch_number);

   num_papers = SQL_singleton_int(conn,
                                  "SELECT count(*) from %s_paper "
                                     "WHERE batch_number = %u;",
                                  electorate_name,
                                  batch_number);

   fprintf(stderr, "num_papers is %u\n", num_papers);

   if (!set_paper_index(conn, batch_number, &paper_id, &paper_index)) {
      fprintf(stderr, "ERROR: Routine set_paper_index failed.\n");
      fprintf(stderr, "Leaving delete_duplicate_paper/1\n");
      return;
   }

   /* Can't delete last paper unless it is ignored (i.e index > b.size)*/
   if (paper_index == num_papers && num_papers <= batch_size) {

      fprintf(stderr,
              "Can't delete last paper unless it is ignored.\n"
              " (i.e. has paper index greater than declared batch size)\n"
              "Need to change the batch size first (currently %u).\n",
              batch_size);

      printf("Can't delete last paper unless it is ignored.\n"
             "(i.e. has paper index greater than declared batch size)\n"
             "Change the batch size first (currently %u).\n",
             batch_size);

      fprintf(stderr, "Leaving delete_duplicate_paper/2\n");
      return;
   }

   if (!set_entry_index(conn, paper_id, &entry_index, operator_id)) {
      fprintf(stderr, "ERROR: Routine set_entry_index failed.\n");
      fprintf(stderr, "Leaving delete_duplicate_paper/3\n");
      return;
   }

   delete_paper(conn,
                batch_number,
                paper_index,
                entry_index,
                get_operator_id());

   fprintf(stderr, "Leaving delete_duplicate_paper\n");

} // delete_duplicate_paper()

// ===================================================================
/*
  The routine insert_paper() is used to insert a paper into the middle
   of a set of papers for a specified entry index.
  The following actions are performed:
  - get index of paper where insertion is to occur
  - if index is invalid, then
  -    reject insertion request
  - get entry index for where insertion is to occur
  - if the entry index is invalid, then
  -    reject insertion request
  - retrieve the necessary paper information from the database
  - get the batch size
  - determine the number of papers to be processed
  - if the number of papers is zero, then
  -    reject the insertion request
  - if the insertion point is greater than the number of papers, then
  -    reject the insertion request
  - if the number of papers is equal or greater than the batch size, then
  -    reject the insertion request
  - if the insertion request was not rejected, then
  -    call get_new_entry_index()
  -    for each paper in the specified entry index do
  -       if the paper index is less than then insertion point, then
  -          call copy_entry_across()
  -          call update_entry()
  -       else if the paper index equals the insertion point, then
  -            call get_other_entry_id()
  -            call copy_entry_across() // other active entry to
                                        //  the new entry index
  -            call update_entry()
  -            call copy_entry_up()     // from specified entry index
                                        //  to the new entry index
  -            call update_entry()
*/
void insert_paper(      PGconn       *conn,
                  const unsigned int  batch_number) {

         PGresult     *result;
         unsigned int  db_query_entry_id;
         unsigned int  entry_index;
         unsigned int  new_entry_index;
         unsigned int  paper_index;
         int           batch_size;
         int           db_query_paper_id;
         int           db_query_paper_index;
         int           i;
         int           num_rows;
         int           num_papers;
         int           other_entry_index;
	 /* SIPL 2011: Changed type of paper_id to conform to paramter type. */
         /* int           paper_id; */
	 unsigned int           paper_id;
         char          *db_query_operator_id;
         char          temp_operator_id[OPERATOR_ID_LEN + 1];
         bool          copy_up = false;

   const char         *electorate_name = (char*) get_voter_electorate()->name;


   fprintf(stderr, "\nEntered insert_paper\n"
                     "====================\n");
   fprintf(stderr, "    batch_number .. %u\n", batch_number);
   fprintf(stderr, "    electorate_name '%s'\n", electorate_name);

   if (!set_paper_index(conn, batch_number, &paper_id, &paper_index)) {
      fprintf(stderr, "ERROR: Routine set_paper_index failed\n.");
      fprintf(stderr, "Leaving insert_paper/1\n");
      return;
   }

   fprintf(stderr, "paper_id    is %d\n", paper_id);
   fprintf(stderr, "paper_index is %d\n", paper_index);

   if (!set_entry_index(conn, paper_id, &entry_index, temp_operator_id)) {
      fprintf(stderr, "ERROR: Routine set_entry_index failed.\n");
      fprintf(stderr, "Leaving insert_paper/2\n");
      return;
   }

   fprintf(stderr, "entry_index is %d\n", entry_index);
   fprintf(stderr, "temp_operator_id is '%s'\n", temp_operator_id);


   /* retrieve all entries posessing an <entry_index> of each paper */

   fprintf(stderr,
           "\nIssue sql query: SELECT p.index, p.id, e.id, e.operator_id "
              "FROM %s_paper p, %s_entry e\n"
              "    WHERE p.batch_number = %u "
              "AND e.paper_id = p.id AND e.index = %u;\n",
           electorate_name, electorate_name,
           batch_number,    entry_index);

   result = SQL_query(conn,
                      "SELECT p.index, p.id, e.id, e.operator_id "
                        "FROM   %s_paper p, %s_entry e "
                        "WHERE  p.batch_number = %u "
                        "AND    e.paper_id     = p.id "
                        "AND    e.index        = %u;",
                      electorate_name,
                      electorate_name,
                      batch_number,
                      entry_index);

   num_rows = PQntuples(result);
   fprintf(stderr, "num_rows %d of data found\n", num_rows);

   begin(conn);

   /* Don't want to see other sessions updates while in transaction */
   fprintf(stderr,
           "\nIssue sql command: "
           "SET TRANSACTION ISOLATION LEVEL SERIALIZABLE;\n");
   SQL_command(conn, "SET TRANSACTION ISOLATION LEVEL SERIALIZABLE;");

   /* record insert details */
   log_batch_operation(conn, batch_number, (enum batch_op) INSERT,
                       (int) paper_index,  (int) entry_index);

   /* declared batch size */
   batch_size = get_batch_size(conn, batch_number);
   fprintf(stderr, "batch_size is %d\n", batch_size);

   /* actual batch_size */
   fprintf(stderr,
           "\nIssue sql query: SELECT count(*) from %s_paper "
              "WHERE batch_number = %u;\n",
           electorate_name,
           batch_number);

   num_papers = SQL_singleton_int(conn,
                                  "SELECT count(*) from %s_paper "
                                     "WHERE batch_number = %u;",
                                  electorate_name,
                                  batch_number);
   fprintf(stderr, "num_papers is %d\n", num_papers);

   if (num_rows == 0) {
      fprintf(stderr,
              "WARNING: There are no existing entries for batch_number %d.\n",
              batch_number);

      printf("There are no existing entries.\n");

   } else if (paper_index > num_papers) {

        fprintf(stderr,
                "Insertion position (%d) is greater than the "
                   "number of papers (%u).\n",
                paper_index, num_papers);

        printf("The specified index (%u) is too high. "
                  "There are only %u papers.\n",
               paper_index, num_papers);

     } else if (num_rows >= batch_size) {
          fprintf(stderr,
                  "The number papers (%d) is >= batch_size (%u).\n"
                  "The batch size needs to be increased first.\n",
                  num_papers, batch_size);

          printf("The number of papers (%d) is to large compared to the "
                    "batch size (%u).\n"
                    "Increase the batch size first.\n",
                 num_papers, batch_size);

     } else {
          fprintf(stderr,
                  "paper_index (%u) <= num_papers (%u) "
                     "< batch_size (%u)\n",
                  paper_index, num_papers, batch_size);

          new_entry_index = get_new_entry_index(conn,
                                                result,
                                                num_rows,
                                                electorate_name);
          for (i = 0; i < num_rows; i++) {
             fprintf(stderr, "\n*******************************************\n");
             fprintf(stderr, "db row = %u\n", i);

             db_query_paper_index = atoi(PQgetvalue(result, i, 0));
             db_query_paper_id    = atoi(PQgetvalue(result, i, 1));
             db_query_entry_id    = atoi(PQgetvalue(result, i, 2));
             db_query_operator_id =      PQgetvalue(result, i, 3);

             fprintf(stderr, "   db_query_paper_index %d\n",
                     db_query_paper_index);
             fprintf(stderr, "   db_query_paper_id .. %d\n",
                     db_query_paper_id);
             fprintf(stderr, "   db_query_entry_id .. %u\n",
                     db_query_entry_id);
             fprintf(stderr, "   db_query_operator_id '%s'\n",
                     db_query_operator_id);

             if ((!copy_up) && (db_query_paper_index == paper_index)) {
                copy_up = true;
                other_entry_index = get_other_entry_id (conn,
                                                        paper_index,
                                                        entry_index,
                                                        batch_number,
                                                        electorate_name);
                copy_entry_across(conn,
                                  -1 * other_entry_index,
                                  db_query_paper_id,
                                  new_entry_index,
                                  batch_number,
                                  get_operator_id(),
                                  electorate_name);

                update_entry(conn,
                             db_query_paper_index,
                             entry_index,
                             new_entry_index,
                             batch_number,
                             electorate_name);
             }

             if (copy_up) {
                copy_entry_up(conn,
                              db_query_entry_id,
                              db_query_paper_index,
                              new_entry_index,
                              batch_number,
                              db_query_operator_id,
                              electorate_name);
                update_entry(conn,
                             db_query_paper_index + 1,
                             entry_index,
                             new_entry_index,
                             batch_number,
                             electorate_name);
             } else {
                  copy_entry_across(conn,
                                    db_query_entry_id,
                                    db_query_paper_id,
                                    new_entry_index,
                                    batch_number,
                                    db_query_operator_id,
                                    electorate_name);
                  update_entry(conn,
                               db_query_paper_index,
                               entry_index,
                               new_entry_index,
                               batch_number,
                               electorate_name);
               }
          }//end for (i = 0; i < num_rows; i++)
      }
   PQclear(result);
   commit(conn);

   fprintf(stderr, "Leaving insert_paper\n");

} // insert_paper()

// ===================================================================
/*
  The routine append_paper() is used to append a paper at the end of
   a specified entry index.
  If a paper exists for the paper index one beyond the number of papers
   for the specified entry index for the other active entry, then
   a copy will be made of that paper.
  If there isn't a paper, then an entry will be made in the paper table
   for the electorate, and a copy will be made of the last paper for
   the specified entry index.
  The following actions will be performed:
  - call get_user_entry_index()
  - get the number of entries
  - if entry index is invalid, then
  -   reject append request
  - get list of papers for the specified entry index
  - if the number of papers is zero, then
  -    reject append request
  - if the number of papers is equal or greater than the batch size, then
  -    reject append request
  - if the append request was not rejected, then
  -    call get_new_entry_index()
  -    for each paper in entry index do
  -       call copy_entry_across()
  -       call update_entry()
  -    if there is a paper index above the number of papers for entry index,
  -     then
  -      call get_id_of_paper() for the next paper
  -      call get_other_entry_id()
  -      call copy_entry_across() from the other active entry
  -    else
  -       call create_empty_paper() to create an entry in the paper table
  -       get information from the last paper at entry index
  -       call copy_entry_up() from the last paper at entry index
*/
void append_paper(      PGconn       *conn,
                  const unsigned int  batch_number) {

         PGresult     *result;
         unsigned int  db_query_entry_id;
         unsigned int  entry_index;
         unsigned int  new_entry_index;
         unsigned int  paper_index;
         int           batch_size;
         int           db_query_paper_id;
         int           db_query_paper_index;
         int           i;
         int           num_entries;
         int           num_rows;
         int           num_papers;
         int           other_entry_index;
         int           paper_id;
         char         *db_query_operator_id;

   const char         *electorate_name = (char*) get_voter_electorate()->name;


   fprintf(stderr, "\nEntered append_paper (APap)\n"
                     "====================\n");
   fprintf(stderr, "    batch_number .. %u\n", batch_number);
   fprintf(stderr, "\nAPap: electorate_name is '%s'\n", electorate_name);

   entry_index = get_user_entry_index();
   fprintf(stderr, "entry_index is %u\n", entry_index);

   fprintf(stderr,
           "\nAPap: Issue sql query: "
              "SELECT MAX(e.index) FROM %s_entry e, %s_paper p\n"
              "     WHERE p.batch_number = %u AND e.paper_id = p.id "
              "AND p.index = 1;\n",
           electorate_name, electorate_name,
           batch_number);

   num_entries = (unsigned int) SQL_singleton_int(
                                   conn,
                                   "SELECT MAX(e.index) "
                                      "FROM %s_entry e, %s_paper p "
                                      "WHERE p.batch_number = %u "
                                      "AND e.paper_id = p.id AND p.index = 1;",
                                   electorate_name, electorate_name,
                                   batch_number);

   if ((entry_index < 1) || (entry_index > num_entries)) {
      fprintf(stderr,
              "APap: ERROR: entry_index is invalid (batch: %u, entry_index: %u).\n",
              batch_number,
              entry_index);

      printf("Entry Index invalid (batch: %u, entry_index: %u).\n",
             batch_number, entry_index);

      fprintf(stderr, "APap: Leaving append_paper/1\n");
      return;
   }

   fprintf(stderr, "APap: entry_index is %d\n", entry_index);

   /* retrieve all entries posessing an <entry_index> of each paper */

   fprintf(stderr,
           "\nAPap: Issue sql query: SELECT p.index, p.id, e.id, e.operator_id "
              "FROM %s_paper p, %s_entry e\n"
              "    WHERE p.batch_number = %u "
              "AND e.paper_id = p.id AND e.index = %u;\n",
           electorate_name, electorate_name,
           batch_number,    entry_index);

   result = SQL_query(conn,
                      "SELECT p.index, p.id, e.id, e.operator_id "
                        "FROM   %s_paper p, %s_entry e "
                        "WHERE  p.batch_number = %u "
                        "AND    e.paper_id     = p.id "
                        "AND    e.index        = %u;",
                      electorate_name, electorate_name,
                      batch_number,    entry_index);

   num_rows   = PQntuples(result);
   fprintf(stderr, "APap: num_rows %d of data found\n", num_rows);

   begin(conn);

   /* Don't want to see other sessions updates while in transaction */
   fprintf(stderr,
           "\nAPap: Issue sql command: "
           "SET TRANSACTION ISOLATION LEVEL SERIALIZABLE;\n");
   SQL_command(conn, "SET TRANSACTION ISOLATION LEVEL SERIALIZABLE;");

   /* record insert details */
   log_batch_operation(conn, batch_number, (enum batch_op) APPEND,
                       (int) num_rows,  (int) entry_index);

   /* declared batch size */
   batch_size = get_batch_size(conn, batch_number);
   fprintf(stderr, "APap: batch_size is %d\n", batch_size);

   /* actual batch_size */
   fprintf(stderr,
           "\nAPap: Issue sql query: SELECT count(*) from %s_paper "
              "WHERE batch_number = %u;\n",
           electorate_name,
           batch_number);

   num_papers = SQL_singleton_int(conn,
                                  "SELECT count(*) from %s_paper "
                                     "WHERE batch_number = %u;",
                                  electorate_name,
                                  batch_number);
   fprintf(stderr, "APap: num_papers is %d\n", num_papers);

   if (num_rows == 0) {
      fprintf(stderr,
              "APap: WARNING: There are no existing entries for batch_number %d.\n",
              batch_number);

      printf("There are no existing entries.\n");

     } else if (num_rows >= batch_size) {
          fprintf(stderr,
                  "APap: The number papers (%d) is >= batch_size (%u).\n"
                  "The batch size needs to be increased first.\n",
                  num_papers, batch_size);

          printf("The number of papers (%d) is to large compared to the "
                    "batch size (%u).\n"
                    "Increase the batch size first.\n",
                 num_papers, batch_size);

     } else {
          new_entry_index = get_new_entry_index(conn,
                                                result,
                                                num_rows,
                                                electorate_name);
          for (i = 0; i < num_rows; i++) {
             fprintf(stderr, "\n******************************************\n");
             fprintf(stderr, "APap: db row = %u\n", i);

             db_query_paper_index = atoi(PQgetvalue(result, i, 0));
             db_query_paper_id    = atoi(PQgetvalue(result, i, 1));
             db_query_entry_id    = atoi(PQgetvalue(result, i, 2));
             db_query_operator_id =      PQgetvalue(result, i, 3);

             fprintf(stderr, "APap:    db_query_paper_index %d\n",
                             db_query_paper_index);
             fprintf(stderr, "APap:    db_query_paper_id .. %d\n",
                             db_query_paper_id);
             fprintf(stderr, "APap:    db_query_entry_id .. %u\n",
                             db_query_entry_id);
             fprintf(stderr, "APap:    db_query_operator_id '%s'\n",
                             db_query_operator_id);

             copy_entry_across(conn,
                               db_query_entry_id,
                               db_query_paper_id,
                               new_entry_index,
                               batch_number,
                               db_query_operator_id,
                               electorate_name);
             update_entry(conn,
                          db_query_paper_index,
                          entry_index,
                          new_entry_index,
                          batch_number,
                          electorate_name);
          } //copy the current information

          fprintf(stderr, "\n---------------------------------------------\n");
          // Now append a new entry

          paper_index = num_rows + 1;
          if (num_papers == num_rows) {
             fprintf(stderr, "APap:1A Need to create a new paper.\n");

             // Need to create a new paper.
             paper_id = create_empty_paper(conn,
                                           paper_index,
                                           batch_number,
                                           electorate_name);
             fprintf(stderr,
                     "\nAPap:1A Issue sql query: "
                       "SELECT e.id FROM %s_paper p, %s_entry e\n"
                       "WHERE p.batch_number = %u AND e.paper_id = p.id "
                       "AND e.index = %u AND p.index = %u;\n",
                     electorate_name, electorate_name,
                     batch_number,    entry_index,
                     num_papers);

             db_query_entry_id = SQL_singleton_int(conn,
                                    "SELECT e.id FROM %s_paper p, %s_entry e "
                                       "WHERE p.batch_number = %u "
                                       "AND e.paper_id = p.id "
                                       "AND e.index = %u "
                                       "AND p.index = %u;",
                                    electorate_name, electorate_name,
                                    batch_number,    entry_index,
                                    num_papers);
             copy_entry_up(conn,
                           db_query_entry_id,
                           num_papers,
                           new_entry_index,
                           batch_number,
                           get_operator_id(),
                           electorate_name);
          } else {
               fprintf(stderr,
                       "\nAPap:2 Issue sql request: "
                       "SELECT id from %s_paper "
                       "WHERE batch_number = %u AND index = %u;\n",
                       electorate_name,
                       batch_number, paper_index);

               paper_id = SQL_singleton_int(conn,
                                            "SELECT id from %s_paper "
                                               "WHERE batch_number = %u "
                                               "AND index = %u;",
                                            electorate_name,
                                            batch_number, paper_index);

               fprintf(stderr, "APap:2 paper_id is %u\n", paper_id);
               other_entry_index = get_other_entry_id (conn,
                                                       paper_index,
                                                       new_entry_index,
                                                       batch_number,
                                                       electorate_name);
               fprintf(stderr, "APap:2 other_entry_index is %u\n", other_entry_index);

               if (other_entry_index > 0) {
                  copy_entry_across(conn,
                                    -1 * other_entry_index,
                                    paper_id,
                                    new_entry_index,
                                    batch_number,
                                    get_operator_id(),
                                    electorate_name);
               } else {
                    /*
                      For this case there is a problem with the 'other' entry
                       so we must copy up.
                      There may be a problem if there is only one entry for a
                       paper and it is not an active entry.
                    */
                    fprintf(stderr,
                             "\nAPap:2B Issue sql query: "
                               "SELECT e.id FROM %s_paper p, %s_entry e\n"
                               "WHERE p.batch_number = %u AND e.paper_id = p.id "
                               "AND e.index = %u AND p.index = %u;\n",
                             electorate_name, electorate_name,
                             batch_number,    entry_index,
                             num_rows);

                     db_query_entry_id = SQL_singleton_int(conn,
                                            "SELECT e.id FROM %s_paper p, %s_entry e "
                                               "WHERE p.batch_number = %u "
                                               "AND e.paper_id = p.id "
                                               "AND e.index = %u "
                                               "AND p.index = %u;",
                                            electorate_name, electorate_name,
                                            batch_number,    entry_index,
                                            num_rows);
                    fprintf(stderr, "APap:2B db_query_entry_id is %d\n", db_query_entry_id);

                    copy_entry_up(conn,
                                  db_query_entry_id,
                                  num_rows,
                                  new_entry_index,
                                  batch_number,
                                  get_operator_id(),
                                  electorate_name);
                 }
            }

          update_entry(conn,
                       paper_index,
                       entry_index,
                       new_entry_index,
                       batch_number,
                       electorate_name);

       } //end if
   PQclear(result);
   commit(conn);

   fprintf(stderr, "Leaving append_paper\n");

} // append_paper()

// ===================================================================
/*
  The routine check_operator_ids_ok() determines whether there are any
   papers in a batch where the current operator (a Supervisor) created
   both of the active entries.
  If a match is found, then the routine returns a value of false, otherwise
   it returns true.
  The following actions occur:
  - get the number of papers in the batch
  - get the batch size
  - if the number of papers is greater than the batch size, then
  -    issue a warning message
  -    restrict processing to the batch size
  - for each paper in the batch do
  -    get the entry indexes for the active entries
  -    get the operator id associated with each active entry
  -    if the operator ids match, and they match the id of the operator
        committing the batch, then
  -       return false
  - return true
*/
bool check_operator_ids_ok (      PGconn       *conn,
                            const unsigned int  batch_number,
                            const char         *electorate_name,
                            const char         *committing_operator) {

   PGresult     *result             = NULL;
   PGresult     *paper_ids_result;
   /* entry_id1 and entry_id2 were (wrongly) unsigned; see
      Bugzilla issue 197. */
   int  entry_id1          = 0;
   int  entry_id2          = 0;
   unsigned int  i;
   int           batch_size;
   int           num_paper_id_rows;
   int           num_rows           = 0;
   int           paper_id           = 0;
   int           paper_index        = 0;
   int           temp               = 0;
   char         *operator_id1       = NULL;
   char         *operator_id2       = NULL;
   bool          return_value       = true;

   fprintf(stderr, "\nEntered check_operator_ids_ok\n"
                     "=============================\n");
   fprintf(stderr, "    batch_number ...... %u\n", batch_number);
   fprintf(stderr, "    electorate_name ... '%s'\n", electorate_name);
   fprintf(stderr, "    committing_operator '%s'\n", committing_operator);

   fprintf(stderr,
           "\nIssue sql query: "
              "SELECT index, id FROM %s_paper WHERE  batch_number = %u;\n",
           electorate_name,
           batch_number);

   paper_ids_result = SQL_query(conn,
                                "SELECT index, id FROM %s_paper "
                                    "WHERE batch_number = %u;",
                                electorate_name,
                                batch_number);

   num_paper_id_rows = PQntuples(paper_ids_result);
   fprintf(stderr,
           "There are %u rows of paper_ids\n",
           num_paper_id_rows);

   batch_size = get_batch_size(conn, batch_number);
   fprintf(stderr, "batch_size is %d\n", batch_size);

   if (num_paper_id_rows > batch_size) {
      fprintf(stderr,
              "\nWARNING: Number of paper IDs (%u) is greater then the "
                 "batch size (%u). Only checking upto batch size.\n",
              num_paper_id_rows, batch_size);

      num_paper_id_rows = batch_size;
   }

   for (i = 0; i < num_paper_id_rows; i++) {
      paper_index = atoi(PQgetvalue(paper_ids_result, i, 0));
      paper_id    = atoi(PQgetvalue(paper_ids_result, i, 1));

      fprintf(stderr, "\n\n***********************************************\n");
      fprintf(stderr, "db row = %u\n", i);
      fprintf(stderr, "   paper_index %d\n", paper_index);
      fprintf(stderr, "   paper_id .. %d\n", paper_id);

      fprintf(stderr,
              "\nIssue sql query: "
                 "SELECT entry_id1, entry_id2 "
                 "FROM %s_paper WHERE id = %u;\n",
              electorate_name,
              paper_id);

      result = SQL_query(conn,
                         "SELECT entry_id1, entry_id2 "
                            "FROM %s_paper WHERE id = %u;",
                         electorate_name,
                         paper_id);

      num_rows = PQntuples(result);
      if (num_rows != 1) {
         fprintf(stderr,
                  "DATABASE ERROR: Incorrect number of rows (%d) when "
                     "requesting entry_id1, entry_id2 (paper_id %u)\n",
                 num_rows,
                 paper_id);
         entry_id1 = 1;
         entry_id2 = 2;

      } else {
           entry_id1 = atoi(PQgetvalue(result, 0, 0));
           entry_id2 = atoi(PQgetvalue(result, 0, 1));
        }

      fprintf(stderr,
              "entry_id1 is %d, entry_id2 is %d\n",
              entry_id1,
              entry_id2);

      /* No need for this function to worry about the
         case where either entry_id1 or entry_id2 is
         -1, because the missing paper has already been noted
         in commit_batch()'s
         earlier call to find_errors_in_batch().
         See Bugzilla issue 197.
       */
      if ((entry_id1 != -1) && (entry_id2 != -1)) {
        fprintf(stderr,
              "\nIssue sql query: "
                 "SELECT operator_id FROM %s_entry "
                 "WHERE index = %u AND paper_id = %u;\n",
              electorate_name,
              entry_id1,
              paper_id);

        result = SQL_query(conn,
                         "SELECT operator_id FROM %s_entry "
                            " WHERE index = %u AND paper_id = %u;",
                         electorate_name,
                         entry_id1,
                         paper_id);

        num_rows = PQntuples(result);
        if (num_rows != 1) {
          fprintf(stderr,
                 "DATABASE ERROR: Incorrect number of rows (%d) when "
                    "requesting operator_id (entry_id1 %u).\n",
                 num_rows,
                 entry_id1);
        } //error

        operator_id1 = PQgetvalue(result, 0, 0);
        fprintf(stderr, "operator_id1 is '%s'\n", operator_id1);

        fprintf(stderr,
              "\nIssue sql query: "
                 "SELECT operator_id FROM %s_entry "
                 "WHERE index = %u AND paper_id = %u;\n",
              electorate_name,
              entry_id2,
              paper_id);

        result = SQL_query(conn,
                         "SELECT operator_id FROM %s_entry "
                            " WHERE index = %u AND paper_id = %u;",
                         electorate_name,
                         entry_id2,
                         paper_id);

      num_rows = PQntuples(result);
      if (num_rows != 1) {
         fprintf(stderr,
                 "DATABASE ERROR: Incorrect number of rows (%d) when "
                    "requesting operator_id (entry_id2 %u)\n",
                 num_rows,
                 entry_id2);
      } //error

      operator_id2 = PQgetvalue(result, 0, 0);
      fprintf(stderr, "operator_id2 is '%s'\n", operator_id2);

      fprintf(stderr,
              "\npaper_index %u, paper_id %u, "
                 "entry_id1 %d is %s, entry_id2 %d is %s - %s\n",
              paper_index, paper_id, entry_id1, operator_id1, entry_id2,
              operator_id2, committing_operator);

      if (strcmp(operator_id1, operator_id2) == 0)
         if (strcmp(operator_id1, committing_operator) == 0) {
            fprintf(stderr,
                    "\nIssue sql query: "
                       "SELECT index FROM %s_paper "
                       "WHERE  batch_number = %u AND id = %u;\n",
                    electorate_name,
                    batch_number,
                    paper_id);

            result = SQL_query(conn,
                               "SELECT index FROM %s_paper "
                                  " WHERE batch_number = %u AND id = %u;",
                               electorate_name,
                               batch_number,
                               paper_id);

            num_rows = PQntuples(result);
            if (num_rows != 1) {
               fprintf(stderr,
                       "DATABASE ERROR: Incorrect number of rows (%d) "
                          "for paper_id %u. Should be 1 row.\n",
                       num_rows,
                       paper_id);
               temp = 0;
            } else
                 temp = atoi(PQgetvalue(result, 0, 0));

            fprintf(stderr,
                    "\nERROR: Operator '%s' "
                       "modified both active entries of paper %u, "
                       "paper_index %d.\n"
                       "Another Supervisor needs to approve batch %u.\n",
                    committing_operator,
                    paper_id,
                    temp,
                    batch_number);
            return_value = false;
            break;
         } // error operator_id1 = operator_id2 = committing_operator
      }
   }// for (i) loop

   PQclear(paper_ids_result);
   PQclear(result);

   fprintf(stderr, "\nLeaving check_operator_ids_ok - returning ");
   if (return_value) fprintf(stderr, "true\n");
   else              fprintf(stderr, "false\n");

   return return_value;

} // check_operator_ids_ok()
