/* This file is (C) copyright 2007 Software Improvements, Pty Ltd */

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

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <common/database.h>
#include <common/evacs.h>
#include "report_common_routines.h"

// The size of the fonts used for the rports
//  TABLE_DESC_FONT_SIZE   - Used for the table's title
//  TITLE_FONT_SIZE        - Used for the title row of the table.
//  CANDIDATE_FONT_SIZE    - Used for the name of candidates.
//  PARTY_FONT_SIZE        - Used for the party/group's abbrivated name.
//  NUMBER_FONT_SIZE       - Used for numbers.
//  FOOTER_FONT_SIZE       - Used for the date and page numbers at the
//                            bottom of each page
//
#define TABLE_DESC_FONT_SIZE         10
#define TITLE_FONT_SIZE               8
#define CANDIDATE_FONT_SIZE           8
#define PARTY_FONT_SIZE               8
#define NUMBER_FONT_SIZE              8
#define FOOTER_FONT_SIZE              8

// The sizes of the columns in the table, values are in millimetres
//
#define CANDIDATE_COLUMN_WIDTH      (unsigned int) (POINTS_IN_MM * 47.0)
#define PARTY_COLUMN_WIDTH          (unsigned int) (POINTS_IN_MM * 11.0)
#define POLLING_PLACE_COLUMN_WIDTH  (unsigned int) (POINTS_IN_MM * 21.0)

// The height of the rows in the column.
// The title row is higher then the other rows.
//
#define TITLE_ROW_HEIGHT            (unsigned int) 24
#define ROW_HEIGHT                  (unsigned int) 12

// The following values indicate vertical offsets to be used
//  when writing text to the title row of the table.
//  TITLE_TOP_LINE_OFFSET    - Offset, from the top of the row, for the
//                              first line of two lines of text.
//  TITLE_CENTRE_LINE_OFFSET - Offset, from the top of the row, for
//                              text when there is only one line of text.
//  TITLE_BOTTOM_LINE_OFFSET - Offset, from the top of the row, for the
//                              second line of two lines of text.
//
#define TITLE_TOP_LINE_OFFSET       (unsigned int)  2
#define TITLE_CENTRE_LINE_OFFSET    (unsigned int)  8
#define TITLE_BOTTOM_LINE_OFFSET    (unsigned int) 12

#define START_Y                     A4_PAGE_HEIGHT - (unsigned int) (POINTS_IN_MM * 25.0)

#define COUNT_NUMBER_FONT           "Helvetica-Bold"

#define MAX_POLLING_PLACES_PER_PAGE 5

#define ROW_COL_ARRAY_SIZE          8

// The following values indicate the position in an
//  array of integers of various values associated with
//  an two dimentional array used to hold the information
//  to be printed in a table. (The information is collected
//  before the table is generated).
// The array is of size ROW_COL_ARRAY_SIZE.
// The array is named 'row_data', and the information in 'row_data'
//  refers to row information in 'preferences[][]'.
// The array 'row_data' exists to reduce the number of parameters
//  being passed to various routines.
//
//  Index Name                        Identifies the row containing:
//  ----------                        ------------------------------
//  RPP_CODES_INDEX                 - polling place codes (polling_place.code)
//  RFIRST_CANDIDATE_INDEX          - the candidate index of the first candidate
//                                     for the current electorate (candidate.index)
//  RLAST_CANDIDATE_INDEX           - the last candidate index (candidate.index)
//                                    'preferences[row_data[RFIRST_CANDIDATE_INDEX]]
//                                                [col_data[CCANDIDATE_CODES_INDEX]]'
//                                    to
//                                    'preferences[row_data[RLAST_CANDIDATE_INDEX]]
//                                                [col_data[CCANDIDATE_CODES_INDEX]]'
//                                    is the list of candidate.index values for which
//                                    first preference information is being obtained.
//  RCNT_FORMAL_VOTES_INDEX         - where the count of formal votes for a polling place
//                                     is to be stored
//  RCNT_INFORMAL_VOTES_INDEX       - where the count of informal votes for a polling place
//                                     is to be stored.
//  RPP_TOTAL_INDEX                 - where the count of formal and informal votes for
//                                    a polling place is to be stored.
//  NOTE:
//    preferences[row_data[RCNT_FORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]
//    preferences[row_data[RCNT_INFORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]
//    preferences[row_data[RPP_TOTAL_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]
//   contain the count of formal, informal, and total votes for the electorate.
//
//  RROW_SIZE                       - contains a value: the number of rows
//                                     in 'preference'.
//  RNUM_CANDIDATES                 - contains a value: holds the number of
//                                     candidates.
//
#define RPP_CODES_INDEX             0
#define RFIRST_CANDIDATE_INDEX      1
#define RLAST_CANDIDATE_INDEX       2
#define RCNT_FORMAL_VOTES_INDEX     3
#define RCNT_INFORMAL_VOTES_INDEX   4
#define RPP_TOTAL_INDEX             5
#define RROW_SIZE                   6
#define RNUM_CANDIDATES             7

// The following values indicate the position in an
//  array of integers of various values associated with
//  an two dimentional array used to hold the information
//  to be printed in a table. (The information is collected
//  before the table is generated).
// The array is of size ROW_COL_ARRAY_SIZE.
// The array is named 'col_data', and the information in 'col_data'
//  refers to column information in 'preferences[][]'.
// The array 'col_data' exists to reduce the number of parameters
//  being passed to various routines.
//
//  Index Name                        Identifies the column containing:
//  ----------                        ---------------------------------
//  CCANDIDATE_CODES_INDEX          - candidate codes (candidate.index)
//  CPARTY_CODES_INDEX              - party codes (candidate.party_index)
//  CFIRST_PPLACE_INDEX             - the first of the set of polling place
//                                     codes (polling_place.code)
//  CLAST_PPLACE_INDEX              - the last of the set of polling place
//                                     codes (pollig_place.code)
//  CCNT_1ST_PREF_INDEX             - the sum of the number of first preferences
//                                     for a candidate for all polling places.
//  CCOL_SIZE                       - contains a value: the number of columns
//                                     in 'preferences'.
//  CNUM_PPLACES                    - contains a value: the number of polling places
//
#define CCANDIDATE_CODES_INDEX      0
#define CPARTY_CODES_INDEX          1
#define CFIRST_PPLACE_INDEX         2
#define CLAST_PPLACE_INDEX          3
#define CCNT_1ST_PREF_INDEX         4
#define CCOL_SIZE                   5
#define CNUM_PPLACES                6

// The following structure is used to hold the file's global data.
struct {

   // The files created.

   FILE         *out; // the postscript file
   FILE         *raw; // holds information for the TSV file

   // The starting horizontal position for the
   //  current report.

   int           x_start_pos;

   // The current position on the page

   int           current_x_pos;
   int           current_y_pos;
   //char         *electorate_name;

   // Saved positions to be used in drawing both
   //  vertical and horizontal lines on the current
   //  page.

   unsigned int  y_pos_start_candidates;
   unsigned int  y_pos_start_totals;
   unsigned int  y_pos_end_totals;
   unsigned int  x_pos_right_edge;

   // The accumulative counts for all electorates

   unsigned int  total_formal_votes;
   unsigned int  total_informal_votes;
   unsigned int  total_total_votes;
} global_data;

// ---------------------------------------------------------------------------
/*
  Open a postscript file.
  There is one file per electorate.
  Only one file is open at a time.
*/
static void open_ps_file(const char *time_string,
                         const char *electorate_name) {

   char *table4_name;

   fprintf(stderr, "\nEntered open_ps_file\n");
   fprintf(stderr, "   time_string: '%s'\n", time_string);

   table4_name      = malloc(sizeof(char) * (strlen("/tmp/table4.ps") + strlen(electorate_name) + 2));
   sprintf(table4_name, "%s%s%s", "/tmp/table4.", electorate_name, ".ps");

   global_data.out   = create_postscript_a4_page(table4_name,
                                                 time_string,
                                                 "First preference votes by polling place");
   fflush(global_data.out);
} // open_ps_file()


// ---------------------------------------------------------------------------
/*
   The routine 'open_raw_file' is used to open the data file to be used to hold
    information needed to to create a TSV file.
   There is one file for each electorate.
   Only one file is open at a time.
*/
static void open_raw_file(const char *electorate_name) {

   char *table4_name;

   fprintf(stderr, "\nEntered open_raw_file (OpnF)\n");
   fprintf(stderr, "   electorate_name: '%s'\n", electorate_name);

   table4_name      = malloc(sizeof(char) * (strlen("/tmp/table4.dat") + strlen(electorate_name) + 2));
   sprintf(table4_name, "%s%s%s", "/tmp/table4.", electorate_name, ".dat");
   global_data.raw  = fopen(table4_name, "w");
   free(table4_name);

   if (!global_data.raw) {
      fprintf(stderr,
              "OpnF: Could not open /tmp/table4.dat for writing: %s - Terminating Program\n",
              strerror(errno));
      close_log_file();
      bailout("Could not open /tmp/table4.dat for writing: %s\n",
              strerror(errno));
   }
   fprintf(stderr, "OpnF: Leaving open_files\n");
} // open_raw_file()

// ===========================================================================
/*
  The routine 'get_first_preference' is used to return an identifier
   to a candidate with the first preference.
  The routines parameters are:
   preference_list - a string containing the preferences, in numerical order
   candidate_index - returns the identifier to the candidate with the first
                      preference for a formal vote.
   party_index     - returns the identifer to the party of the candidate with
                      the first preference for a formal vote.
   informal        - set to True if the vote is informal; i.e. the number of
                      preferences = 0. Otherwise a value of False is returned.
*/
static void  get_first_preference(char         *preference_list,
                                  unsigned int *candidate_index,
                                  unsigned int *party_index,
                                  bool         *informal) {

   unsigned int       i, num_prefs;
   char              *pref_ptr;
   struct preference *preference_data;

   // fprintf(stderr, "\nEntered get_first_preference\n");
   // fprintf(stderr, "   preference_list: '%s'\n", preference_list);

   *candidate_index = 0;
   *party_index     = 0;
   *informal        = true;

   preference_data  = malloc(sizeof(struct preference));
   for (pref_ptr = (char *)preference_list, num_prefs = 0;
        strlen(pref_ptr) >= DIGITS_PER_PREF;
        pref_ptr += DIGITS_PER_PREF*sizeof(char), num_prefs++);

   /* Sanity Check: pref_ptr should be at end of string */
   if (strlen(pref_ptr))
      bailout("malformed pref list '%s'\n",
              preference_list);


   /* Decode preference list into memory structure */
   for (pref_ptr = preference_list, i = 0;
        i < num_prefs;
        i++, pref_ptr += DIGITS_PER_PREF*sizeof(char)) {

      sscanf(pref_ptr, (const char *)"%2u%2u%2u",
             &preference_data->prefnum,
             &preference_data->group_index,
             &preference_data->db_candidate_index);

      // fprintf(stderr, "i=%u\n", i);
      // fprintf(stderr, "prefnum: .......... %u\n", preference_data->prefnum);
      // fprintf(stderr, "group_index: ...... %u\n", preference_data->group_index);
      // fprintf(stderr, "db_candidate_index: %u\n", preference_data->db_candidate_index);

      if (preference_data->prefnum == 1) {
         *candidate_index = preference_data->db_candidate_index;
         *party_index     = preference_data->group_index;
         *informal        = false;
         free(preference_data);
         // fprintf(stderr, "Leaving get_first_preference\n");
         return;
         }
   }
   free(preference_data);
   // fprintf(stderr, "ERROR: Leaving get_first_preference - didn't find 1st preference\n");
} //get_prefs_for_entry

// ---------------------------------------------------------------------------
/*
  The routine 'get_preference_information' is used to obtain the number of first
   preferences received by each candidate, in a specified electorate, from each
   polling place.
  The routine also calculate the number of formal, informal, and total votes for
   each polling place, as well as the number of first preferences received by each
   candidate from all polling places.
*/
static void get_preference_information (      PGconn        *conn,
                                              unsigned int  number_of_electorates,
                                              char         *electorate_names[number_of_electorates],
                                        const unsigned int  current_electorates_code,
                                        const unsigned int  row_data[ROW_COL_ARRAY_SIZE],
                                        const unsigned int  row_size,
                                        const unsigned int  col_data[ROW_COL_ARRAY_SIZE],
                                        const unsigned int  col_size,
                                              unsigned int  preferences[row_size][col_size]) {

   PGresult     *result_preference_list;

   unsigned int number_of_papers;
   unsigned int candidate_index;
   unsigned int electorate_index;
   unsigned int paper_index;
   unsigned int polling_place_index;

   unsigned int row_polling_place_index    = row_data[RPP_CODES_INDEX];
   unsigned int row_first_candidate        = row_data[RFIRST_CANDIDATE_INDEX];
   unsigned int row_pp_count_formal_votes  = row_data[RCNT_FORMAL_VOTES_INDEX];
   unsigned int number_of_candidates       = row_data[RNUM_CANDIDATES];

   unsigned int col_candidate_index        = col_data[CCANDIDATE_CODES_INDEX];
   unsigned int col_party_index            = col_data[CPARTY_CODES_INDEX];
   unsigned int col_first_polling_place    = col_data[CFIRST_PPLACE_INDEX];
   unsigned int col_count_1st_preferences  = col_data[CCNT_1ST_PREF_INDEX];
   unsigned int number_of_polling_places   = col_data[CNUM_PPLACES];

   unsigned int *candidate_number = malloc(sizeof(unsigned int));
   unsigned int *party_number     = malloc(sizeof(unsigned int));
   bool         *informal         = malloc(sizeof(bool));

   // fprintf(stderr, "\nEntered get_preference_information\n");
   // fprintf(stderr, "   number_of_electorates: ... %u\n", number_of_electorates);
   // fprintf(stderr, "   electorate_code: ......... %u\n", electorate_code);
   // fprintf(stderr, "   number_of_candidates: .... %u\n", number_of_candidates);
   // fprintf(stderr, "   number_of_polling_places:  %u\n", number_of_polling_places);
   // fprintf(stderr, "   row_size: ................ %u\n", row_size);
   // fprintf(stderr, "   col_size: ................ %u\n", col_size);

   // fprintf(stderr, "row_polling_place_index is . %u\n", row_polling_place_index);
   // fprintf(stderr, "row_first_candidate is ..... %u\n", row_first_candidate);
   // fprintf(stderr, "row_pp_count_formal_votes is %u\n", row_pp_count_formal_votes);
   // fprintf(stderr, "col_candidate_index is ..... %u\n", col_candidate_index);
   // fprintf(stderr, "col_party_index is ......... %u\n", col_party_index);
   // fprintf(stderr, "col_first_polling_place is . %u\n", col_first_polling_place);
   // fprintf(stderr, "col_count_1st_preferences is %u\n", col_count_1st_preferences);

   *candidate_number = 0;
   *party_number     = 0;
   *informal         = true;

   // check the confirmed votes table for each elecorate

   for (electorate_index = 0; electorate_index < number_of_electorates; electorate_index++) {

      // for each polling place

      for (polling_place_index = col_first_polling_place;
           polling_place_index < col_first_polling_place + number_of_polling_places;
           polling_place_index++) {

         // fprintf(stderr,
         //         "Issue sql query: SELECT c.preference_list FROM %s_confirmed_vote c, batch b\n"
         //                                    "WHERE c.batch_number = b.number "
         //                                       "AND b.polling_place_code = %u "
         //                                       "AND b.electorate_code = %u;\n",
         //                                    electorate_names[electorate_index],
         //                                    preferences[row_polling_place_index][polling_place_index],
         //                                    current_electorates_code);

         // Obtain the preferences for the current electorate

         result_preference_list = SQL_query(conn,
                                            "SELECT c.preference_list FROM %s_confirmed_vote c, batch b "
                                            "WHERE c.batch_number = b.number "
                                               "AND b.polling_place_code = %u "
                                               "AND b.electorate_code = %u;",
                                            electorate_names[electorate_index],
                                            preferences[row_polling_place_index][polling_place_index],
                                            current_electorates_code);

         number_of_papers = PQntuples(result_preference_list);

         // fprintf(stderr, "number_of_papers is %u\n", number_of_papers);
         preferences[row_data[RPP_TOTAL_INDEX]][polling_place_index] += number_of_papers;

         // fprintf(stderr, "Total votes preferences[%u][%u] is %u\n",
         //         row_data[RPP_TOTAL_INDEX], polling_place_index,
         //         preferences[row_data[RPP_TOTAL_INDEX]][polling_place_index]);

         for (paper_index = 0; paper_index < number_of_papers; paper_index++) {
            get_first_preference(PQgetvalue(result_preference_list, paper_index, 0),
                                 candidate_number,
                                 party_number,
                                 informal);
            if (*informal) {
               preferences[row_data[RCNT_INFORMAL_VOTES_INDEX]][polling_place_index]++;

            } else {

                 // Need to match up the entry in preferences[][] for the candidate returned by
                 //  'get_first_preference'.

                 for (candidate_index = row_first_candidate;
                      candidate_index < row_first_candidate + number_of_candidates;
                      candidate_index++) {

                    if ((preferences[candidate_index][col_candidate_index] == *candidate_number)
                         && (preferences[candidate_index][col_party_index] == *party_number) ) {
                        preferences[candidate_index][polling_place_index]++;
                        // fprintf(stderr, "inc preferences[%u][%u] to %u\n",
                        //      candidate_index, polling_place_index,
                        //      preferences[candidate_index][polling_place_index]);
                    }
                 }
              }
         } //for paper_index
      } //for polling_place_index
   }//for electorate_index

   // fprintf(stderr, "count for polling place\n");

   for (polling_place_index = col_first_polling_place;
        polling_place_index < col_first_polling_place + number_of_polling_places;
        polling_place_index++) {
      for (candidate_index = row_first_candidate;
           candidate_index < row_first_candidate + number_of_candidates;
           candidate_index++) {
         preferences[row_pp_count_formal_votes][polling_place_index]
           += preferences[candidate_index][polling_place_index];
      }

      // fprintf(stderr,
      //         " cnt of formal votes for preferences[%u][%u] is %u\n",
      //         row_pp_count_formal_votes, polling_place_index,
      //         preferences[row_pp_count_formal_votes][polling_place_index]);
   }


   // fprintf(stderr, "count for candidates\n");

   for (candidate_index = row_first_candidate;
        candidate_index < row_data[RPP_TOTAL_INDEX] + 1;
        candidate_index++) {
      for (polling_place_index = col_first_polling_place;
           polling_place_index < col_first_polling_place + number_of_polling_places;
           polling_place_index++) {
         preferences[candidate_index][col_count_1st_preferences]
            += preferences[candidate_index][polling_place_index];
      }
   }

   // print the data structure
/*
   for (candidate_index = 0; candidate_index < row_size; candidate_index++) {
        printf("%3u: ", candidate_index);
        fprintf(stderr, "%3u: ", candidate_index);
      for (polling_place_index = 0;
           polling_place_index < col_size;
           polling_place_index++) {
        printf("%6u", preferences[candidate_index][polling_place_index]);
        fprintf(stderr, "%6u", preferences[candidate_index][polling_place_index]);
      }
      printf("\n");
   }
*/

   // fprintf(stderr, "Leaving get_preference_information\n");
} // get_preference_information()

// ===========================================================================
/*
   The routine 'draw_number_box' is used to write a number in a box for a
    postscript file.
   The routine converts the number to a string and has the string written.
   The routine's parameters are:

   - out    - identifies the postscript file to which the number is to be
               drawn
   - value  - the number to be drawn.
   - fill   - indicates whether the box is to be coloured grey.
*/
/* SIPL 2011: Commented out the following function,
 *       because it is never used, and thus generated a compiler warning.
 */
/* static unsigned int draw_number_box(FILE         *out, */
/*                                     unsigned int  value, */
/*                                     bool          fill) { */

/*    char valstring[INT_CHARS+1]; */

/*    // fprintf(stderr, "\nEntered draw_number_box\n"); */

/*    sprintf(valstring, "%u", value); */

/*    return draw_text_box(out, */
/*                         POLLING_PLACE_COLUMN_WIDTH, */
/*                         ROW_HEIGHT, */
/*                         valstring, */
/*                         NUMBER_FONT_SIZE, */
/*                         ORIENT_HORIZONTAL, */
/*                         JUSTIFY_RIGHT, */
/*                         fill); */
/* } */ // draw_number_box()

// ===========================================================================
/*
   The routine 'draw_title_cell' is used to draw a single cell in the
    title row of the table.
   The title row is higher than normal rows, and may have either one or
    two lines of text.
   The routine's parameters are:
     out     - identifies the postscript file to which the text is to
                be written.
     raw     - identifies the data file created to hold information
                required for a TSV file.
     line1   - the first line of text.
     line2   - the second line of text.
     width   - the width of the cell.
     x_pos   - the current x-axis position on the postscript file.
     y_pos   - the current y-axis position on the postscript file.
*/
static void draw_title_cell (      FILE        *out,
                                   FILE        *raw,
                             const char        *line1,
                             const char        *line2,
                             const unsigned int width,
                             const unsigned int x_pos,
                             const unsigned int y_pos) {

   /* SIPL 2011: commented out return_value, as it is now not used. */
   /* unsigned int return_value; */

   // fprintf(stderr, "\nEntered draw_title_cell\n");
   // fprintf(stderr, "   line1: '%s'\n", line1);
   // fprintf(stderr, "   line2: '%s'\n", line2);
   // fprintf(stderr, "   width: %u\n", width);
   // fprintf(stderr, "   x_pos: %u\n", x_pos);
   // fprintf(stderr, "   y_pos: %u\n", y_pos);

   fprintf(out, "%u %u moveto\n", x_pos, y_pos);

   /* SIPL 2011: commented out return_value, as it is not used subsequently. */
   /* return_value += draw_empty_box(global_data.out, */
   /*                                width, */
   /*                                TITLE_ROW_HEIGHT, */
   /*                                true); */

   draw_empty_box(global_data.out,
                  width,
                  TITLE_ROW_HEIGHT,
                  true);
   /* SIPL 2011: Use strcmp() instead of "!=" to compare strings. */
   /* if (line1 != "") { */
   if (strcmp(line1, "") != 0){

      // The check for line2[0] == '\0' is required because the split
      //  routine, places '\0' at line2[0] to indicate that the string is
      //  empty.
      // However, this is not a null string.

      /* SIPL 2011: Use strcmp() instead of "==" to compare strings. */
      /* if ((line2 == "") || (line2[0] == '\0')) { */
     if ((strcmp(line2,"") == 0) || (line2[0] == '\0')) {
         fprintf(out, "%u %u moveto\n", x_pos, y_pos - TITLE_CENTRE_LINE_OFFSET);
      } else {
           fprintf(out, "%u %u moveto\n", x_pos, y_pos - TITLE_TOP_LINE_OFFSET);
        }
      write_text(out,
                 width,
                 ROW_HEIGHT,
                 TITLE_FONT_SIZE,
                 line1,
                 ORIENT_HORIZONTAL,
                 JUSTIFY_CENTRE,
                 true);
   }

   /* SIPL 2011: Use strcmp() instead of "!=" to compare strings. */
   /* if (line2 != "") { */
     if (strcmp(line2, "") != 0) {
      fprintf(out, "%u %u moveto\n", x_pos, y_pos - TITLE_BOTTOM_LINE_OFFSET);
      write_text(out,
                 width,
                 ROW_HEIGHT,
                 TITLE_FONT_SIZE,
                 line2,
                 ORIENT_HORIZONTAL,
                 JUSTIFY_CENTRE,
                 true);
   }

   // fprintf(stderr, "Leaving draw_title_cell\n");
} // draw_title_cell()

// ---------------------------------------------------------------------------
/*
  The routine 'split' is used to split a string in two.
  The string is split on the first occurrance of the character defined by the
   input parameter split_on.
*/
static unsigned int split(char *original,
                          char  split_on,
                          char *split1,
                          char *split2) {

   unsigned int flag     = 0;
   unsigned int i        = 0;
   unsigned int j        = 0;

  split1[0] = '\0';
  split2[0] = '\0';

  while (original[i] != '\0') {
     if (flag == 0) {
        if (original[i] == split_on) {
           flag      = 1;
           split1[i] = '\0';
        } else {
           split1[i] = original[i];
          }
     } else {
        split2[j++] = original[i];
     }
     i++;
   }
   split1[i] = '\0';
   split2[j] = '\0';
   return flag;
} // split()

// ---------------------------------------------------------------------------
/*
   The routine 'draw_table_heading' is used the draw the table title and the
    first row of the table.
   The routine's parameters are:

     out       - identifies the postscript file to which data is to be drawn
     raw       - identifies a data file information is to be written for
                  later creation of a TSV file.
     electorate_name -
     number_of_polling_places - contains the number of polling places.
     first_polling_place      - identifies the index, into polling_place_names,
                                 of the first polling place to be listed on the
                                 current page.
     last_polling_place       - identifies the index, into polling_place_names,
                                 of the last polling place to be listed on the
                                 current page.
                                NOTE: if last_polling_place == number_of_polling_places
                                       then this the last column on the last page, and
                                       a title 'Total' is written rather than a polling
                                       place name.
     polling_place_names      - contains the names of all of the polling places.
*/

// The following defines labels for the title row of the table - with the exception of the
//  names of polling places.

#define CANDIDATE_TITLE_TXT "Candidate"
#define PARTY_TITLE_TXT     "Party/"
#define GROUP_TITLE_TXT     "Group"
#define TOTAL_TITLE_TXT     "Total"

#define MAX_POLLING_PLACE_NAME_SIZE  100
#define MAX_TABLE_TITLE_SIZE         100

static unsigned int draw_table_heading(      FILE         *out,
                                             FILE         *raw,
                                             char         *electorate_name,
                                       const unsigned int  number_polling_places,
                                       const unsigned int  first_polling_place,
                                       const unsigned int  last_polling_place,
                                             char         *polling_place_names[number_polling_places]) {

   unsigned int table_x_offset, table_y_offset;
   unsigned int item_counter           = 1;
   unsigned int num_pp_to_list         = last_polling_place - first_polling_place;

   unsigned int return_value           = 0;
   unsigned int x_pos, y_pos;
   int          polling_place_index;
   char         table_title_str[MAX_TABLE_TITLE_SIZE];
   char        *polling_place_name;
   char        *s1                     = (char *) malloc(MAX_POLLING_PLACE_NAME_SIZE * sizeof(char));
   char        *s2                     = (char *) malloc(MAX_POLLING_PLACE_NAME_SIZE * sizeof(char));

   fprintf(stderr, "\nEntered draw_table_heading (DTH)\n");
   fprintf(stderr, "   number_polling_places: %u\n", number_polling_places);
   fprintf(stderr, "   first_polling_place: . %u\n", first_polling_place);
   fprintf(stderr, "   last_polling_place: .. %u\n", last_polling_place);

   fprintf(stderr, "num_pp_to_list is %u\n", num_pp_to_list);


   // Specify the position of the table's title

   table_y_offset = (unsigned int) (POINTS_IN_MM * 5.0);
   table_x_offset = (CANDIDATE_COLUMN_WIDTH + PARTY_COLUMN_WIDTH
                     + (POLLING_PLACE_COLUMN_WIDTH * num_pp_to_list)) / 2;

   fprintf(global_data.out,
           "%u %u moveto\n",
           global_data.x_start_pos + table_x_offset,
           START_Y + table_y_offset);

   fprintf(global_data.out, "gsave /Helvetica-bold findfont ");
   fprintf(global_data.out, "%u scalefont setfont ", TABLE_DESC_FONT_SIZE);
   sprintf(table_title_str, "Table IV - First preference votes by polling place: %s", electorate_name);
   max_length(out, table_title_str);
   fprintf(out, " 2 div neg 0 rmoveto\n");
   fprintf(out, "(%s) show grestore\n", table_title_str);

   x_pos = global_data.current_x_pos;
   y_pos = global_data.current_y_pos;

   // Start drawing the first row of the table

   // a) Candidate Name

   draw_title_cell (out,
                    raw,
                    CANDIDATE_TITLE_TXT,
                    "",
                    CANDIDATE_COLUMN_WIDTH,
                    x_pos,
                    y_pos);
   x_pos += CANDIDATE_COLUMN_WIDTH;

   // b) Party/Group Abbriviation

   draw_title_cell (out,
                    raw,
                    PARTY_TITLE_TXT,
                    GROUP_TITLE_TXT,
                    PARTY_COLUMN_WIDTH,
                    x_pos,
                    y_pos);

   x_pos += PARTY_COLUMN_WIDTH;
   item_counter += first_polling_place;

   // c) Polling Place names, or 'Total'

   for (polling_place_index = first_polling_place;
        polling_place_index < last_polling_place;
        polling_place_index++ ) {

      fprintf(out, "%u %u moveto\n", x_pos, y_pos);

      if (polling_place_index < number_polling_places) {

         // cell contains the name of a polling place

         polling_place_name = sprintf_malloc("%s", polling_place_names[polling_place_index]);
      } else {

           // cell is 'Total'

           polling_place_name = sprintf_malloc("%s", TOTAL_TITLE_TXT);
        }

      split(polling_place_name, ' ', s1, s2);
      draw_title_cell (out,
                       raw,
                       s1,
                       s2,
                       POLLING_PLACE_COLUMN_WIDTH,
                       x_pos,
                       y_pos);
      x_pos += POLLING_PLACE_COLUMN_WIDTH;

      if (polling_place_index < number_polling_places)
         fprintf(raw, "PP:%u:%s\n", polling_place_index, polling_place_name);
   }
   global_data.x_pos_right_edge = x_pos;
   //fprintf(stderr,
           //"DTH: Leaving draw_table_heading: return_value is %u\n",
           //return_value);
   free(s1);
   free(s2);
   return return_value;

} // draw_title_heading()

// ---------------------------------------------------------------------------
/*
  The routine 'end_of_page' is used to handle the actions of completing the
   table for the current page.
  This includes writing the date and page number at the bottom of the page, and
   having the required postscript comments added to the postscript file.
  The routine's parameters are:

    out         - identifies the postscript file.
    page_number - indicates the current page.
    last_page   - if not '0' then this is the last page.
    time_string - time and date that the postscript file was created.
                  It is the time and date written to the bottom of the page.
*/
static void end_of_page(FILE         *out,
                        unsigned int  page_number,
                        unsigned int  last_page,
                        char         *time_string) {

   char page_num_str[30];

   //fprintf(stderr, "\nEntered end_of_page\n");
   //fprintf(stderr, "   page_number: ... %u\n", page_number);
   //fprintf(stderr, "   time_string: ... '%s'\n", time_string);

   fprintf(global_data.out, "/Helvetica findfont ");
   fprintf(global_data.out, "%u scalefont setfont ", FOOTER_FONT_SIZE);

   fprintf(out,
           "%u %u moveto\n",
           (unsigned int) (POINTS_IN_MM * 5.0),
           20);
   fprintf(out, "gsave (%s) show grestore\n", time_string);


   fprintf(out, "%u %u moveto\n", MIDDLE_A4_PAGE_X, 20);
   sprintf(page_num_str, "Page %u", page_number);
   max_length(out, page_num_str);
   fprintf(out, " 2 div neg 0 rmoveto\n");
   fprintf(out, "gsave (%s) show grestore\n", page_num_str);

   a4_page_end_postscript(out, page_number, last_page);

} // end_of_page()

// ===========================================================================
/*
  The routine 'draw_formal_totals' is used to write the row of total formal votes
   for a polling place into the table.
  For the last column, on the last page, the count is for the electorate.
  The routine's parameters are:

     number_of_electorates   - the number of electorates.
     electorate_names        - contains the names of all of the electorates.
     first_polling_place     - the index of the first polling place for which the count
                                of first preferences for each candidate is to be listed.
     last_polling_place      - the index of the last polling place to be listed on the
                                current page.
                               If last_polling_place == the number of polling places, then
                                a count for the electorate will be listed.
     row_data                - identifies where information is in the various rows of the
                                parameter 'preferences'.
     row_size                - the number of rows in the parameter 'preferences'.
     col_data                - identifies where information is in the various columns of
                                the parameter 'preferences'.
     col_size                - the number of columns in the parameter 'preferences'.
     preferences             - contains the number of first preferences for each candidate
                                in each polling place.
                               Also contains count of formal, informal, and total votes, as
                                well as the count of first preferences for each candidate
                                in all polling places.
*/
#define FORMAL_TXT              "Formal"

static unsigned int draw_formal_totals(      unsigned int  number_of_electorates,
                                             char         *electorate_names[number_of_electorates],
                                       const unsigned int  first_polling_place,
                                       const unsigned int  last_polling_place,
                                       const unsigned int  row_data[ROW_COL_ARRAY_SIZE],
                                       const unsigned int  row_size,
                                       const unsigned int  col_data[ROW_COL_ARRAY_SIZE],
                                       const unsigned int  col_size,
                                             unsigned int  preferences[row_size][col_size]) {

   unsigned int return_value = 0;
   unsigned int polling_place_index;
   unsigned int col, row;
   unsigned int number_to_report;
   char         number_string[INT_CHARS+1];


   fprintf(stderr, "\nEntered draw_formal_totals\n");

   // move to the start of the first column of a new row in
   //  the table.

   fprintf(global_data.out,
           "%u %u moveto\n",
           global_data.current_x_pos,
           global_data.current_y_pos);

   // the text 'Formal'

   write_text(global_data.out,
              CANDIDATE_COLUMN_WIDTH,
              ROW_HEIGHT,
              CANDIDATE_FONT_SIZE,
              FORMAL_TXT,
              ORIENT_HORIZONTAL,
              JUSTIFY_LEFT,
              false);

   global_data.current_x_pos += CANDIDATE_COLUMN_WIDTH;

   // skip the Party/Group column; this cell is empty

   global_data.current_x_pos += PARTY_COLUMN_WIDTH;


   // list the totals for each of the polling places on the
   //  current page.

   for (polling_place_index = first_polling_place;
        polling_place_index < last_polling_place;
        polling_place_index++) {

      fprintf(global_data.out,
              "%u %u moveto\n",
              global_data.current_x_pos,
              global_data.current_y_pos);

      col = polling_place_index + col_data[CFIRST_PPLACE_INDEX];

      if (preferences[row_data[RPP_TOTAL_INDEX]][col] > 0) {
         row              = row_data[RCNT_FORMAL_VOTES_INDEX];
         number_to_report = preferences[row][col];

         sprintf(number_string, "%u", number_to_report);
         write_text(global_data.out,
                    POLLING_PLACE_COLUMN_WIDTH,
                    ROW_HEIGHT,
                    NUMBER_FONT_SIZE,
                    number_string,
                    ORIENT_HORIZONTAL,
                    JUSTIFY_RIGHT,
                    false);

         // write the data for later use in creating a TSV file

         if (polling_place_index == col_data[CNUM_PPLACES]) {
            fprintf(global_data.raw,
                    "TOTFOR:%u\n",
                    number_to_report);
         } else {
              fprintf(global_data.raw,
                      "TTFOR:%u:%u\n",
                      polling_place_index,
                      number_to_report);
           }
      }
      global_data.current_x_pos += POLLING_PLACE_COLUMN_WIDTH;
   }

   return return_value;

} // draw_formal_totals()

// ===========================================================================
/*
  The routine 'draw_informal_totals' is used to write the row of total informal votes
   for a polling place into the table.
  For the last column, on the last page, the count is for the electorate.
  The routine's parameters are:

     number_of_electorates   - the number of electorates.
     electorate_names        - contains the names of all of the electorates.
     first_polling_place     - the index of the first polling place for which the count
                                of first preferences for each candidate is to be listed.
     last_polling_place      - the index of the last polling place to be listed on the
                                current page.
                               If last_polling_place == the number of polling places, then
                                a count for the electorate will be listed.
     row_data                - identifies where information is in the various rows of the
                                parameter 'preferences'.
     row_size                - the number of rows in the parameter 'preferences'.
     col_data                - identifies where information is in the various columns of
                                the parameter 'preferences'.
     col_size                - the number of columns in the parameter 'preferences'.
     preferences             - contains the number of first preferences for each candidate
                                in each polling place.
                               Also contains count of formal, informal, and total votes, as
                                well as the count of first preferences for each candidate
                                in all polling places.
*/
#define INFORMAL_TXT "Informal"

static unsigned int draw_informal_totals(      unsigned int  number_of_electorates,
                                               char         *electorate_names[number_of_electorates],
                                         const unsigned int  first_polling_place,
                                         const unsigned int  last_polling_place,
                                         const unsigned int  row_data[ROW_COL_ARRAY_SIZE],
                                         const unsigned int  row_size,
                                         const unsigned int  col_data[ROW_COL_ARRAY_SIZE],
                                         const unsigned int  col_size,
                                               unsigned int  preferences[row_size][col_size]) {

   unsigned int return_value = 0;
   unsigned int polling_place_index;
   unsigned int col, row;
   unsigned int number_to_report;
   char         number_string[INT_CHARS+1];

   fprintf(stderr, "\nEntered draw_informal_totals\n");

   // move to the position of the top left hand courner of the first cell in the row

   fprintf(global_data.out,
           "%u %u moveto\n",
           global_data.current_x_pos,
           global_data.current_y_pos);

   // write the text 'Informal'

   write_text(global_data.out,
              CANDIDATE_COLUMN_WIDTH,
              ROW_HEIGHT,
              CANDIDATE_FONT_SIZE,
              INFORMAL_TXT,
              ORIENT_HORIZONTAL,
              JUSTIFY_LEFT,
              false);

   global_data.current_x_pos += CANDIDATE_COLUMN_WIDTH;

   // Skip the party/group column
   global_data.current_x_pos += PARTY_COLUMN_WIDTH;

   // write the count for each polling place

   for (polling_place_index = first_polling_place;
        polling_place_index < last_polling_place;
        polling_place_index++) {

      fprintf(global_data.out,
              "%u %u moveto\n",
              global_data.current_x_pos,
              global_data.current_y_pos);

      col = polling_place_index + col_data[CFIRST_PPLACE_INDEX];
      row = row_data[RCNT_INFORMAL_VOTES_INDEX];

      if (preferences[row_data[RPP_TOTAL_INDEX]][col] > 0) {
         number_to_report = preferences[row][col];

         sprintf(number_string, "%u", number_to_report);
         write_text(global_data.out,
                    POLLING_PLACE_COLUMN_WIDTH,
                    ROW_HEIGHT,
                    NUMBER_FONT_SIZE,
                    number_string,
                    ORIENT_HORIZONTAL,
                    JUSTIFY_RIGHT,
                    false);

         // write information to the data file that will later
         //  be converted to a TSV file

         if (polling_place_index == col_data[CNUM_PPLACES]) {
            fprintf(global_data.raw,
                    "TOTINF:%u\n",
                    number_to_report);
         } else {
              fprintf(global_data.raw,
                      "TTINF:%u:%u\n",
                      polling_place_index,
                      number_to_report);
           }
      }

      global_data.current_x_pos += POLLING_PLACE_COLUMN_WIDTH;
   }

   return return_value;

} // draw_informal_totals()

// ===========================================================================
/*
  The routine 'draw_total_votes' is used to write the row of the count of formal
   and informal votes for a polling place into the table.
  For the last column, on the last page, the count is for the electorate.
  The routine's parameters are:

     number_of_electorates   - the number of electorates.
     electorate_names        - contains the names of all of the electorates.
     first_polling_place     - the index of the first polling place for which the count
                                of first preferences for each candidate is to be listed.
     last_polling_place      - the index of the last polling place to be listed on the
                                current page.
                               If last_polling_place == the number of polling places, then
                                a count for the electorate will be listed.
     row_data                - identifies where information is in the various rows of the
                                parameter 'preferences'.
     row_size                - the number of rows in the parameter 'preferences'.
     col_data                - identifies where information is in the various columns of
                                the parameter 'preferences'.
     col_size                - the number of columns in the parameter 'preferences'.
     preferences             - contains the number of first preferences for each candidate
                                in each polling place.
                               Also contains count of formal, informal, and total votes, as
                                well as the count of first preferences for each candidate
                                in all polling places.
*/
#define POLLING_PLACE_TOTAL_TXT "Polling place total"

static unsigned int draw_total_votes(      unsigned int  number_of_electorates,
                                           char         *electorate_names[number_of_electorates],
                                     const unsigned int  first_polling_place,
                                     const unsigned int  last_polling_place,
                                     const unsigned int  row_data[ROW_COL_ARRAY_SIZE],
                                     const unsigned int  row_size,
                                     const unsigned int  col_data[ROW_COL_ARRAY_SIZE],
                                     const unsigned int  col_size,
                                           unsigned int  preferences[row_size][col_size]) {

   unsigned int return_value = 0;
   unsigned int polling_place_index;
   unsigned int col, row;
   unsigned int number_to_report;
   char         number_string[INT_CHARS+1];

   fprintf(stderr, "\nEntered draw_total_votes\n");

   // move to the postion of the top left hand courner of the first cell
   //  in the row.

   fprintf(global_data.out,
           "%u %u moveto\n",
           global_data.current_x_pos,
           global_data.current_y_pos);

   // Write the text 'Polling place total'

   write_text(global_data.out,
              CANDIDATE_COLUMN_WIDTH,
              ROW_HEIGHT,
              CANDIDATE_FONT_SIZE,
              POLLING_PLACE_TOTAL_TXT,
              ORIENT_HORIZONTAL,
              JUSTIFY_LEFT,
              false);

   global_data.current_x_pos += CANDIDATE_COLUMN_WIDTH;

   // Skip the Party/Group column

   global_data.current_x_pos += PARTY_COLUMN_WIDTH;

   // write the values

   for (polling_place_index = first_polling_place;
        polling_place_index < last_polling_place;
        polling_place_index++) {


      fprintf(global_data.out,
              "%u %u moveto\n",
              global_data.current_x_pos,
              global_data.current_y_pos);

      if (polling_place_index < col_data[CLAST_PPLACE_INDEX]) {

         col              = polling_place_index + col_data[CFIRST_PPLACE_INDEX];
         row              = row_data[RPP_TOTAL_INDEX];
         number_to_report = preferences[row][col];

         if (number_to_report > 0) {
            sprintf(number_string, "%u", number_to_report);
            write_text(global_data.out,
                       POLLING_PLACE_COLUMN_WIDTH,
                       ROW_HEIGHT,
                       NUMBER_FONT_SIZE,
                       number_string,
                       ORIENT_HORIZONTAL,
                       JUSTIFY_RIGHT,
                       false);

            // write data to file that will later be converted to a
            //  TSV file

            if (polling_place_index == col_data[CNUM_PPLACES]) {
               fprintf(global_data.raw,
                       "TOTTOT:%u\n",
                       number_to_report);
            } else {
                 fprintf(global_data.raw,
                         "TOT:%u:%u\n",
                         polling_place_index,
                         number_to_report);
              }
        }

         global_data.current_x_pos += POLLING_PLACE_COLUMN_WIDTH;
      }
   }

   return return_value;

} // draw_total_votes()

// ===========================================================================
/*
  The routine 'draw_lines' is used to draw line between columns on the table and
   at the boundary of the table.
  The routine also draws the horizontal line at the bottom of the table and the
   line separating the candidates from the totals.
*/
static void draw_lines(void) {

   unsigned int i, x_pos;

   // horizontal line under candidates

   x_pos = global_data.x_start_pos;

   draw_line(global_data.out,
             x_pos,
             global_data.y_pos_start_totals,
             global_data.x_pos_right_edge,
             global_data.y_pos_start_totals);

   // horizontal line at bottom of table

   draw_line(global_data.out,
             x_pos,
             global_data.y_pos_end_totals,
             global_data.x_pos_right_edge,
             global_data.y_pos_end_totals);

   // draw the vertical lines

   // a) left hand side of table

   draw_line(global_data.out,
             x_pos,
             global_data.y_pos_start_candidates,
             x_pos,
             global_data.y_pos_end_totals);
   x_pos += CANDIDATE_COLUMN_WIDTH;

   draw_line(global_data.out,
             x_pos,
             global_data.y_pos_start_candidates,
             x_pos,
             global_data.y_pos_end_totals);
   x_pos += PARTY_COLUMN_WIDTH;

   draw_line(global_data.out,
             x_pos,
             global_data.y_pos_start_candidates,
             x_pos,
             global_data.y_pos_end_totals);

   for (i = 0; i < MAX_POLLING_PLACES_PER_PAGE; i++) {
      x_pos += POLLING_PLACE_COLUMN_WIDTH;
      if (x_pos <= global_data.x_pos_right_edge) {
         draw_line(global_data.out,
                   x_pos,
                   global_data.y_pos_start_candidates,
                   x_pos,
                   global_data.y_pos_end_totals);
      }
   }
} // draw_lines()


// ===========================================================================

// The follwing values define the position of various data items in an
// SQL request result record.

#define SQL_01_CANDIDATE_NAME        0
#define SQL_01_CANDIDATE_INDEX       1
#define SQL_01_CANDIDATE_PARTY_INDEX 2
#define SQL_01_PARTY_ABBREVIATION    3

// ===========================================================================


int main(int argc, char *argv[]) {

   PGconn       *conn;

   PGresult     *result_candidate_names;
   PGresult     *result_electorate_names;
   PGresult     *result_polling_places;

   unsigned int  item_index;
   unsigned int  first_polling_place;
   unsigned int  last_polling_place;
   unsigned int  return_value;
   unsigned int  number_of_candidates;
   unsigned int  number_of_electorates;
   unsigned int  number_of_polling_places;
   unsigned int  number_to_report;

   unsigned int  polling_places_referenced;

   unsigned int  candidate_index;
   unsigned int  electorate_index;
   unsigned int  page_index;
   unsigned int  polling_place_index;
   unsigned int  cindex, pindex;
   unsigned int  col, row;

   char         *db_query_candidate_name;
   char         *db_query_party_abbreviation;
   char          number_string[INT_CHARS+1];
   char          time_string[TIME_STR_LEN];

   bool          finished_electorate;
   unsigned int  col_data[ROW_COL_ARRAY_SIZE];
   unsigned int  row_data[ROW_COL_ARRAY_SIZE];
   unsigned int  COL_SIZE, ROW_SIZE;

   printf("\nCreating table 4 - First preference votes by polling place (for all electorates)\n");
   get_date_and_time(time_string, TIME_STR_LEN);
   memset(&global_data, 0, sizeof(global_data));

   open_log_file ("create_report_4", time_string);
   fprintf(stderr, "\nEntered main (First preference votes by polling place)\n");


   // conn = connect_db_host(DATABASE_NAME, SERVER_ADDRESS);
   conn = connect_db(DATABASE_NAME);
   if (conn == NULL) {
      fprintf(stderr,
              "ERROR: Unable to connect to database: '%s' - PROGRAM TERMINATING\n",
              DATABASE_NAME);
      fflush(stderr);
      close_log_file();
      bailout("Can't connect to database: '%s'\n",
              DATABASE_NAME);
   }


   // Get list of electorates

   /*
   fprintf(stderr,
           "\nIssue sql query: SELECT  code, name FROM electorate "
              "ORDER by name;\n");
   */

   result_electorate_names = SQL_query(conn,
                      "SELECT  code, name FROM electorate "
                      "ORDER BY name;");

   number_of_electorates = PQntuples(result_electorate_names);
   // fprintf(stderr, "number_of_electorates is %u\n", number_of_electorates);


   unsigned int  electorate_codes[number_of_electorates];
   char         *electorate_names[number_of_electorates];

   for (electorate_index = 0; electorate_index < number_of_electorates; electorate_index++) {
      electorate_codes[electorate_index] = atoi(PQgetvalue(result_electorate_names, electorate_index, 0));
      electorate_names[electorate_index] =      PQgetvalue(result_electorate_names, electorate_index, 1);
   }


   // Obtain list of Polling Places, then determine the number of
   //  pages required to print the information


   /*
   fprintf(stderr,
           "\nIssue sql query: SELECT  code, name, electorate_code FROM polling_place "
              "ORDER by name;\n");
   */

   result_polling_places = SQL_query(conn,
                                     "SELECT  code, name, electorate_code "
                                     "FROM polling_place "
                                     "ORDER BY name;");

   number_of_polling_places = PQntuples(result_polling_places);
   // fprintf(stderr, "number_of_polling_places is %u\n", number_of_polling_places);

   unsigned int  polling_place_codes[number_of_polling_places];
   char         *polling_place_names[number_of_polling_places];

   for (polling_place_index = 0; polling_place_index < number_of_polling_places; polling_place_index++) {
      polling_place_codes[polling_place_index] = atoi(PQgetvalue(result_polling_places, polling_place_index, 0));
      polling_place_names[polling_place_index] =      PQgetvalue(result_polling_places, polling_place_index, 1);
   }


   // determine the position on the page to place the table (top left hand courner).
   // The table is centred horizontally in the page.

   global_data.x_start_pos = MIDDLE_A4_PAGE_X
                             - (CANDIDATE_COLUMN_WIDTH + PARTY_COLUMN_WIDTH
                                + (POLLING_PLACE_COLUMN_WIDTH * MAX_POLLING_PLACES_PER_PAGE)) / 2;

   if (global_data.x_start_pos < 0) {
      fprintf(stderr, "Too many polling places to fit across an A4 page. Terminating Program\n");
      close_log_file();
      bailout ("Too many polling places to fit across an A4 page.");
   }

   polling_places_referenced = 0;

   // Process each electorate

   for (electorate_index = 0;
        electorate_index < number_of_electorates;
        electorate_index++) {
      printf("\nProcessing electorate - %s\n", electorate_names[electorate_index]);

      open_ps_file(time_string, electorate_names[electorate_index]);
      open_raw_file(electorate_names[electorate_index]);

      finished_electorate = false;
      page_index          = 1;

      fprintf(global_data.raw,
              "EL:0:%s\n",
              electorate_names[electorate_index]);
      /*
      fprintf(stderr,
              "\nIssue sql query: SELECT c.name, c.index, c.party_index, p.abbreviation "
                                             "FROM candidate c, party p\n"
                                             "WHERE c.electorate_code = %u "
                                               "AND c.electorate_code = p.electorate_code "
                                               "AND c.party_index     = p.index\n"
                                             "ORDER BY c.name;\n",
                                          electorate_codes[electorate_index]);
      */

      result_candidate_names = SQL_query(conn,
                                         "SELECT c.name, c.index, c.party_index, p.abbreviation "
                                            "FROM candidate c, party p "
                                            "WHERE c.electorate_code = %u "
                                              "AND c.electorate_code = p.electorate_code "
                                              "AND c.party_index     = p.index "
                                            "ORDER BY c.party_index, c.index;",
                                         electorate_codes[electorate_index]);

      number_of_candidates = PQntuples(result_candidate_names);

      row_data[RPP_CODES_INDEX]           = 0;
      row_data[RFIRST_CANDIDATE_INDEX]    = row_data[RPP_CODES_INDEX]         + 1;
      row_data[RLAST_CANDIDATE_INDEX]     = row_data[RFIRST_CANDIDATE_INDEX]  + number_of_candidates - 1;
      row_data[RCNT_FORMAL_VOTES_INDEX]   = row_data[RLAST_CANDIDATE_INDEX]   + 1;
      row_data[RCNT_INFORMAL_VOTES_INDEX] = row_data[RCNT_FORMAL_VOTES_INDEX] + 1;
      row_data[RPP_TOTAL_INDEX]           = row_data[RCNT_INFORMAL_VOTES_INDEX] + 1;
      row_data[RROW_SIZE]                 = row_data[RPP_TOTAL_INDEX]         + 1;
      row_data[RNUM_CANDIDATES]           = number_of_candidates;
      ROW_SIZE = row_data[RROW_SIZE];

      col_data[CCANDIDATE_CODES_INDEX]  = 0;
      col_data[CPARTY_CODES_INDEX]      = col_data[CCANDIDATE_CODES_INDEX] + 1;
      col_data[CFIRST_PPLACE_INDEX]     = col_data[CPARTY_CODES_INDEX]     + 1;
      col_data[CLAST_PPLACE_INDEX]      = col_data[CFIRST_PPLACE_INDEX]    + number_of_polling_places - 1;
      col_data[CCNT_1ST_PREF_INDEX]     = col_data[CLAST_PPLACE_INDEX]     + 1;
      col_data[CCOL_SIZE]               = col_data[CCNT_1ST_PREF_INDEX]    + 1;
      col_data[CNUM_PPLACES]            = number_of_polling_places;
      COL_SIZE = col_data[CCOL_SIZE];

      unsigned int preferences[ROW_SIZE][COL_SIZE];
      memset(&preferences, 0, sizeof(preferences));

      /*
      fprintf(stderr, "row of polling place index is ... %u\n", row_data[RPP_CODES_INDEX]);
      fprintf(stderr, "row of first candidate is ....... %u\n", row_data[RFIRST_CANDIDATE_INDEX]);
      fprintf(stderr, "row of last candidate is ........ %u\n", row_data[RLAST_CANDIDATE_INDEX]);
      fprintf(stderr, "row of pp count formal votes is   %u\n", row_data[RCNT_FORMAL_VOTES_INDEX]);
      fprintf(stderr, "row of pp count informal votes is %u\n", row_data[RCNT_INFORMAL_VOTES_INDEX]);
      fprintf(stderr, "row of pp total votes is ........ %u\n", row_data[RPP_TOTAL_INDEX]);
      fprintf(stderr, "row size is ..................... %u\n", row_data[RROW_SIZE]);
      fprintf(stderr, "number of candidates is ......... %u\n", row_data[RNUM_CANDIDATES]);

      fprintf(stderr, "col of candidate_index is ....... %u\n", col_data[CCANDIDATE_CODES_INDEX]);
      fprintf(stderr, "col of party_index is ........... %u\n", col_data[CPARTY_CODES_INDEX]);
      fprintf(stderr, "col of first_polling_place is ... %u\n", col_data[CFIRST_PPLACE_INDEX]);
      fprintf(stderr, "col of last_polling_place is .... %u\n", col_data[CLAST_PPLACE_INDEX]);
      fprintf(stderr, "col of count_1st_preferences is   %u\n", col_data[CCNT_1ST_PREF_INDEX]);
      fprintf(stderr, "col size is ..................... %u\n", col_data[CCOL_SIZE]);
      fprintf(stderr, "number of polling places is ..... %u\n", col_data[CNUM_PPLACES]);
      */

      // store list of candidate IDs, and the ID of their associated Party/Group in 'preferences'

      for (cindex = row_data[RFIRST_CANDIDATE_INDEX]; cindex < row_data[RLAST_CANDIDATE_INDEX] + 1; cindex++) {
        preferences[cindex][col_data[CCANDIDATE_CODES_INDEX]] = atoi(PQgetvalue(result_candidate_names,
                                                                                cindex - row_data[RFIRST_CANDIDATE_INDEX],
                                                                                SQL_01_CANDIDATE_INDEX));
        preferences[cindex][col_data[CPARTY_CODES_INDEX]]     = atoi(PQgetvalue(result_candidate_names,
                                                                                cindex - row_data[RFIRST_CANDIDATE_INDEX],
                                                                                SQL_01_CANDIDATE_PARTY_INDEX));
      }

      // store the polling place codes in 'preferences'

      for (pindex = col_data[CFIRST_PPLACE_INDEX]; pindex < col_data[CLAST_PPLACE_INDEX] + 1; pindex++)
        preferences[row_data[RPP_CODES_INDEX]][pindex]
           = polling_place_codes[pindex - col_data[CFIRST_PPLACE_INDEX]];

      // get the information, for the entire electorate, that is to be listed in the table

      get_preference_information(conn,
                                 number_of_electorates,
                                 electorate_names,
                                 electorate_codes[electorate_index],
                                 row_data,
                                 ROW_SIZE,
                                 col_data,
                                 COL_SIZE,
                                 preferences);

      // create the table.
      // This will require a number of pages.

      first_polling_place = 0;
      last_polling_place  = MAX_POLLING_PLACES_PER_PAGE;

      while (!finished_electorate) {
         fprintf(stderr, "Start a new page %u\n", page_index);

         // start of a new page

         global_data.current_x_pos = global_data.x_start_pos;
         global_data.current_y_pos = START_Y;

         page_start_postscript(global_data.out, page_index);

         draw_table_heading(global_data.out,
                            global_data.raw,
                            electorate_names[electorate_index],
                            number_of_polling_places,
                            first_polling_place,
                            last_polling_place,
                            polling_place_names);

         global_data.current_x_pos          = global_data.x_start_pos;
         global_data.current_y_pos         -= TITLE_ROW_HEIGHT;
         return_value                       = 0;
         global_data.y_pos_start_candidates = global_data.current_y_pos;

         for (candidate_index = 0; candidate_index < number_of_candidates; candidate_index++) {
            // fprintf(stderr, " for candidate index %u of number_of_candidates %u\n",
            //                 candidate_index, number_of_candidates);

            item_index = 1;
            db_query_candidate_name     = PQgetvalue(result_candidate_names,
                                                     candidate_index,
                                                     SQL_01_CANDIDATE_NAME);

            db_query_party_abbreviation = PQgetvalue(result_candidate_names,
                                                     candidate_index,
                                                     SQL_01_PARTY_ABBREVIATION);

            /*
            fprintf(stderr, "main:    candidate_index .. %u\n", candidate_index);
            fprintf(stderr, "main:    db_query_candidate_name: ... '%s'\n", db_query_candidate_name);
            fprintf(stderr, "main:    db_query_party_abbreviation: '%s'\n", db_query_party_abbreviation);
            */

            // The name of the candidate

            fprintf(global_data.out,
                    "%u %u moveto\n",
                    global_data.current_x_pos,
                    global_data.current_y_pos);

            write_text(global_data.out,
                       CANDIDATE_COLUMN_WIDTH,
                       ROW_HEIGHT,
                       CANDIDATE_FONT_SIZE,
                       db_query_candidate_name,
                       ORIENT_HORIZONTAL,
                       JUSTIFY_LEFT,
                       false);

            fprintf(global_data.raw,
                    "CAN:%u:0:%s\n",
                    candidate_index,
                    db_query_candidate_name);

            global_data.current_x_pos += CANDIDATE_COLUMN_WIDTH;

            // The Party/Group's abbriviation

            fprintf(global_data.out,
                    "%u %u moveto\n",
                    global_data.current_x_pos,
                    global_data.current_y_pos);

            write_text(global_data.out,
                       PARTY_COLUMN_WIDTH,
                       ROW_HEIGHT,
                       PARTY_FONT_SIZE,
                       db_query_party_abbreviation,
                       ORIENT_HORIZONTAL,
                       JUSTIFY_CENTRE,
                       false);

            fprintf(global_data.raw,
                    "CAN:%u:1:%s\n",
                    candidate_index,
                    db_query_party_abbreviation);

            global_data.current_x_pos += PARTY_COLUMN_WIDTH;

            // the polling place information

            item_index += first_polling_place;
            for (polling_place_index = first_polling_place;
                 polling_place_index < last_polling_place;
                 polling_place_index++) {

               fprintf(global_data.out,
                       "%u %u moveto\n",
                       global_data.current_x_pos,
                       global_data.current_y_pos);

               row = candidate_index     + row_data[RFIRST_CANDIDATE_INDEX];
               col = polling_place_index + col_data[CFIRST_PPLACE_INDEX];
               if (col <= col_data[CLAST_PPLACE_INDEX]) {
                  number_to_report = preferences[row][col];
                  if (preferences[row_data[RPP_TOTAL_INDEX]][col] > 0) {

                     // list the count of first preferences for this candidate for this
                     //  polling place

                     /*
                     fprintf(stderr, "[row(%u) = candidate_index(%u) + row_first_candidate(%u)]",
                                     row, candidate_index, row_data[RFIRST_CANDIDATE_INDEX]);
                     fprintf(stderr, "[col(%u) = polling_place_index(%u) + col_first_polling_place(%u)] is %u\n",
                                     col, polling_place_index, col_data[CFIRST_PPLACE_INDEX], number_to_report);
                     */
                     sprintf(number_string, "%u", number_to_report);
                     write_text(global_data.out,
                                POLLING_PLACE_COLUMN_WIDTH,
                                ROW_HEIGHT,
                                NUMBER_FONT_SIZE,
                                number_string,
                                ORIENT_HORIZONTAL,
                                JUSTIFY_RIGHT,
                                false);
                  }
                  fprintf(global_data.raw,
                          "DT:%u:%u:%u\n",
                          candidate_index,
                          polling_place_index,
                          number_to_report);
               } else {

                    // this is the last column.
                    // The information listed is not the count of first preferences for
                    //  a polling place.
                    // The information is the count of first preferences for all polling
                    // places

                    number_to_report = preferences[row][col];
                    sprintf(number_string, "%u", number_to_report);
                    write_text(global_data.out,
                               POLLING_PLACE_COLUMN_WIDTH,
                               ROW_HEIGHT,
                               NUMBER_FONT_SIZE,
                               number_string,
                               ORIENT_HORIZONTAL,
                               JUSTIFY_RIGHT,
                               false);

                    fprintf(global_data.raw,
                            "T1P:%u:%u\n",
                            candidate_index,
                            number_to_report);
                 }
               global_data.current_x_pos += POLLING_PLACE_COLUMN_WIDTH;
            }

            global_data.current_x_pos  = global_data.x_start_pos;
            global_data.current_y_pos -= ROW_HEIGHT;
         } // finished a page

         fprintf(global_data.out,
                 "%u %u moveto\n",
                 global_data.current_x_pos,
                 global_data.current_y_pos);

         // list the totals: Formal, Informal, Polling place total

         global_data.y_pos_start_totals = global_data.current_y_pos;

         // a) Formal
         draw_formal_totals(number_of_electorates,
                            electorate_names,
                            first_polling_place,
                            last_polling_place,
                            row_data,
                            ROW_SIZE,
                            col_data,
                            COL_SIZE,
                            preferences);
         global_data.current_x_pos  = global_data.x_start_pos;
         global_data.current_y_pos -= ROW_HEIGHT;

         fprintf(global_data.out,
                 "%u %u moveto\n",
                 global_data.current_x_pos,
                 global_data.current_y_pos);

         // b) Informal
         draw_informal_totals(number_of_electorates,
                              electorate_names,
                              first_polling_place,
                              last_polling_place,
                              row_data,
                              ROW_SIZE,
                              col_data,
                              COL_SIZE,
                              preferences);
         global_data.current_x_pos  = global_data.x_start_pos;
         global_data.current_y_pos -= ROW_HEIGHT;

         fprintf(global_data.out,
                 "%u %u moveto\n",
                 global_data.current_x_pos,
                 global_data.current_y_pos);

         // c) Polling place total
         draw_total_votes(number_of_electorates,
                          electorate_names,
                          first_polling_place,
                          last_polling_place,
                          row_data,
                          ROW_SIZE,
                          col_data,
                          COL_SIZE,
                          preferences);

         global_data.current_x_pos  = global_data.x_start_pos;
         global_data.current_y_pos -= ROW_HEIGHT;

         global_data.y_pos_end_totals = global_data.current_y_pos;

         // draw the missing table border and column seperation lines
         draw_lines();

         // update the first and last polling place index values

         if (last_polling_place >= (number_of_polling_places +1)) {

            // Finished the table for the current electorate

            fprintf(stderr, "finished with electorate\n");
            finished_electorate = true;
            end_of_page(global_data.out, page_index, true, time_string);

         } else {

              // At least one more page

              first_polling_place += MAX_POLLING_PLACES_PER_PAGE;
              last_polling_place  += MAX_POLLING_PLACES_PER_PAGE;

              if (last_polling_place > (number_of_polling_places + 1))
                 last_polling_place = number_of_polling_places + 1;

              end_of_page(global_data.out, page_index, false, time_string);
              page_index++;
           }
      } // while (!finished_electorate)

      // display totals on the terminal.
      // Since this program takes some time, the listing of the information
      //  is to indicate to the operator how much the program has completed

      printf("Total Formal Votes for %s is . %8u\n",
             electorate_names[electorate_index],
             preferences[row_data[RCNT_FORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]);
      fprintf(stderr,
              "\nTotal Formal Votes for %s is . %u\n",
              electorate_names[electorate_index],
              preferences[row_data[RCNT_FORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]);

      global_data.total_formal_votes += preferences[row_data[RCNT_FORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]];

      printf("Total Informal Votes for %s is %8u\n",
             electorate_names[electorate_index],
             preferences[row_data[RCNT_INFORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]);
      fprintf(stderr,
              "Total Informal Votes for %s is %u\n",
              electorate_names[electorate_index],
              preferences[row_data[RCNT_INFORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]);

      global_data.total_informal_votes += preferences[row_data[RCNT_INFORMAL_VOTES_INDEX]][col_data[CCNT_1ST_PREF_INDEX]];

      printf("Total Votes for %s is ........ %8u\n",
             electorate_names[electorate_index],
             preferences[row_data[RPP_TOTAL_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]);
      fprintf(stderr,
              "Total Votes for %s is ........ %u\n",
              electorate_names[electorate_index],
              preferences[row_data[RPP_TOTAL_INDEX]][col_data[CCNT_1ST_PREF_INDEX]]);

      global_data.total_total_votes += preferences[row_data[RPP_TOTAL_INDEX]][col_data[CCNT_1ST_PREF_INDEX]];

      close_postscript(global_data.out);
      fclose(global_data.raw);

   } // for each electorate

   // The totals for all electorates.

   printf("\nTotal Formal Votes is . %9u\n",
          global_data.total_formal_votes);

   printf("Total Informal Votes is %9u\n",
          global_data.total_informal_votes);

   printf("Total Votes is ........ %9u\n",
          global_data.total_total_votes);

   fprintf(stderr,
           "\nTotal Formal Votes is . %u\n",
           global_data.total_formal_votes);

   fprintf(stderr,
           "Total Informal Votes is %u\n",
           global_data.total_informal_votes);

   fprintf(stderr,
           "Total Votes is ........ %u\n",
          global_data.total_total_votes);

   close_log_file();
   return 0;
} // report_preferences_by_polling_place()
