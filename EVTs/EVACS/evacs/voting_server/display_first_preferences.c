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

/* This program prompts the user for a password, and displays the
   number of first preferences allocated to each candidate.  */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <crypt.h>
#include <common/database.h>
#include <common/evacs.h>
#include <counting/ballot_iterators.h>
#include <counting/candidate_iterators.h>
#include <counting/report.h>
#include "count_first_preferences.h"
#include "display_first_preferences.h"

#define PASSWORD_LENGTH 8
#define HASH_LENGTH 13

/* SIPL 2011-08-19 String values of the qualifications. */
const char * const qualification_names[] = {
  "pre-poll",
  "polling day"
};

// Prompts the user for a password, returns a hash of the password using crypt
static char *prompt_for_password()
{
  char password[PASSWORD_LENGTH + 1];
  char *password_encrypted;
  int i;
  char c = 0;

  password_encrypted = malloc(sizeof(char)*(HASH_LENGTH + 1));

  fprintf(stderr, "Please enter the password: ");
  // Read up to 8 characters into password
  for(i=0; i<PASSWORD_LENGTH && (c = getchar()) != '\n'; i++) {
    password[i] = c;
  }
  // Append with null
  password[i] = '\0';
  // Discard rest of line
  for (;c != '\n'; c = getchar()) {}

  // Encrypt the password, the extra security from implementing a random salt
  // is not needed here.
  strcpy(password_encrypted, crypt(password, "eV"));
  if (password_encrypted == NULL) {
    printf("Encryption failed");
    return NULL;
  }
  password_encrypted[HASH_LENGTH] = '\0';

  // Erase the plaintext password from memory
  for(i=0; i<PASSWORD_LENGTH + 1; i++) {
    password[i] = '\0';
  }

  return password_encrypted;
}


static bool free_piles(struct candidate *cand, void *unused)
{
  unsigned int i;

  for (i = 0; i < 1; i++)
    if (cand->c[i].pile)
      free_ballot_list(cand->c[i].pile);

  return false;
}

static bool free_candidate(struct candidate *cand, void *unused)
{
  free(cand->name);
  free(cand);
  return false;
}

static void free_group_names(struct group *groups, unsigned int num_groups)
{
  unsigned int i;

  for (i = 0; i < num_groups; i++)
    free(groups[i].name);
}

/* Given the non-NULL electorate, fill in all the groups, return number. */
static unsigned int fetch_groups(PGconn *conn, 
			  const struct electorate *elec,
			  struct group *groups)
{
  PGresult *result;
  unsigned int i;

  result = SQL_query(conn,
		     "SELECT name, abbreviation, index FROM party "
		     "WHERE electorate_code = %u "
		     "ORDER by index;", elec->code);
  for (i = 0; i < PQntuples(result); i++) {
    groups[i].name = strdup(PQgetvalue(result, i, 0));
    groups[i].abbrev = strdup(PQgetvalue(result, i, 1));
    groups[i].group_index = atoi(PQgetvalue(result, i, 2));
  }
  PQclear(result);
  return i;
}

/* Find a group by index */
static struct group *find_group(struct group *groups, unsigned int index)
{
	while (groups->group_index != index)
		groups++;
	return groups;
}

/* Given the group information, return the candidate list */
static struct cand_list *fetch_candidates(PGconn *conn, 
				   const struct electorate *elec,
				   struct group *groups)
{
  struct cand_list *list = NULL;
  unsigned int i;
  PGresult *result;

  /* By returning them in order, we help the scrutiny sheet generation */
  result = SQL_query(conn,
		     "SELECT name, index, party_index FROM candidate "
		     "WHERE electorate_code = %u "
		     "ORDER BY party_index DESC, name DESC;", elec->code);
  for (i = 0; i < PQntuples(result); i++) {
    list = new_cand_list(malloc(sizeof(struct candidate)), list);
    list->cand->name = strdup(PQgetvalue(result, i, 0));
    list->cand->db_candidate_index
      = atoi(PQgetvalue(result, i, 1));
    list->cand->group = find_group(groups,
				   atoi(PQgetvalue(result, i, 2)));
    list->cand->count_when_quota_reached = 0;
    /* We are PREpending to list, so count is backwards */
    list->cand->scrutiny_pos = PQntuples(result) - i - 1;
    /* All piles empty, all totals 0 */
    memset(list->cand->c, 0, sizeof(list->cand->c));
    /* surplus distributed flag: init false */
    list->cand->surplus_distributed=false;
  }
  PQclear(result);
  return list;
}

/* Load a single vote */
static struct ballot *load_vote(PGconn *conn, const char *preference_list)
{
	struct ballot *ballot;
	char *pref_ptr;   
	unsigned int num_preferences=0,i;
	unsigned int pref_number, group_index, db_cand_index;

	for (pref_ptr=(char *)preference_list;
	     strlen(pref_ptr)>=DIGITS_PER_PREF;
	     pref_ptr += DIGITS_PER_PREF*sizeof(char),num_preferences++);
	
	if ( strlen(pref_ptr)) 
		bailout("Malformed preference list: '%s'\n",preference_list);
	
	ballot = malloc(sizeof(*ballot)
			+ sizeof(ballot->prefs[0])*num_preferences);
	ballot->num_preferences = num_preferences;
	ballot->count_transferred = 0;
	
	/* They many not be in order */
	for (pref_ptr=(char *)preference_list, i = 0;
	     i < ballot->num_preferences; 
	     i++,pref_ptr += DIGITS_PER_PREF*sizeof(char) )
	{
		sscanf(pref_ptr,"%2u%2u%2u",&pref_number,&group_index,&db_cand_index);
		
		ballot->prefs[pref_number-1]
			.group_index = group_index;
		ballot->prefs[pref_number-1]
			.db_candidate_index = db_cand_index;
	}
	
	return ballot;
	
}

/* SIPL 2011: Two parameters added: the election date,
              and the qualification (pre-poll or polling day). */
/* Get all the ballots for this electorate */
static struct ballot_list *fetch_ballots(PGconn *conn, 
                                         const struct electorate *elec, 
                                         const char *elec_date, 
                                         const int qualification)
{
  struct ballot_list *list = NULL;
  PGresult *result;
  unsigned int i,num_votes;

  if (qualification == PRE_POLL)
    result = SQL_query(conn,
                       "SELECT preference_list " 
                       "FROM %s_confirmed_vote "
                       "WHERE to_date(time_stamp, 'YYYY-MM-DD HH24:MI:SS') < to_date('%s', 'YYYY-MM-DD'); "
                       , elec->name, elec_date);
  else if (qualification == POLLING_DAY)
    result = SQL_query(conn,
                       "SELECT preference_list " 
                       "FROM %s_confirmed_vote "
                       "WHERE to_date(time_stamp, 'YYYY-MM-DD HH24:MI:SS') = to_date('%s','YYYY-MM-DD'); "
                       , elec->name, elec_date);
  else
    bailout("Wrong option: %d. It must be either 0 (pre-poll) or 1 (polling day).\n", qualification);
  
  num_votes =  PQntuples(result);

  for (i = 0; i < num_votes; i++) {
    list = new_ballot_list( load_vote(conn,PQgetvalue(result, i, 0)),list);
  }
  PQclear(result);
  return list;
}

int main(int argc, char *argv[])
{
  struct ballot_list *ballots;
  PGconn *conn;
  struct election e;
  struct electorate *initial;
  char *password_hash;
  char *valid_password_hash;
  int qualification;

  /* SIPL 2011: Added to command-line arguments to display first preferences
   *            for pre-poll and polling day separately. 
   */
    /* printf("Argc: %d\n", argc); */
    /* printf("Argv[1]: %s\n", argv[1]); */
    /* printf("Argv[2]: %s\n", argv[2]); */
    if (argc != 3)
      bailout("Usage: display_first_preferences <election-date> <pre_poll or polling_day>\n");
  
    qualification = atoi(argv[2]);
    if ((qualification != PRE_POLL) && (qualification != POLLING_DAY))
      bailout("Wrong qualification option: %d. It must be either 0 (pre-poll) or 1 (polling day).\n", qualification);



  /* Connect to the database */
  conn = connect_db(DATABASE_NAME);
  if (conn == NULL) bailout("Can't connect to database:%s\n",
			    DATABASE_NAME);
  valid_password_hash= SQL_singleton(conn,
				     "SELECT password_hash FROM master_data;");
  
  /* Get the password from the user, and compare to password in database */
  password_hash = prompt_for_password();
    fprintf(stderr, "\n");
  if( strcmp(password_hash, valid_password_hash) ) {
    fprintf(stderr, "Invalid password.\n");
    free(password_hash);
    free(valid_password_hash);
    return(-1);
  }
  free(password_hash);
  free(valid_password_hash);

  /* For each electorate, do_count. do_count will print information to the
     screen */
  initial = get_electorates(conn);
  
  /* SIPL 2011: Display indication of pre-poll or polling day on the top.*/
  printf("Summary of first preferences (%s)\n",
         qualification_names[qualification]);
  
  for(e.electorate = initial; e.electorate; e.electorate=e.electorate->next) {
    e.num_groups = fetch_groups(conn, e.electorate, e.groups);
    e.candidates = fetch_candidates(conn, e.electorate, e.groups);
    /* SIPL 2011: Get ballots according to Election Date 
              and Pre-poll or Polling day option */
    ballots = fetch_ballots(conn, e.electorate, argv[1], qualification);

    do_count(&e, ballots, NULL, qualification);
      
    /* free allocated memory */
    for_each_candidate(e.candidates, &free_piles, NULL);
    for_each_candidate(e.candidates, &free_candidate, NULL);
    free_group_names(e.groups, e.num_groups);
    free_cand_list(e.candidates);
  }

  free_electorates(initial);

  PQfinish(conn);
  return 0;
}
