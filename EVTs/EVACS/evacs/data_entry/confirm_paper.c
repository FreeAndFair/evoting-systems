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
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <common/database.h>  
#include <common/batch.h>
#include <common/evacs.h>
#include <common/find_errors.h>
#include <common/current_paper_index.h>
#include <voting_client/vote_in_progress.h>
#include <election_night/update_ens_summaries.h>

#include "confirm_paper.h"

static unsigned int number_of_entries;

static int cmp_prefnum(const void *v1, const void *v2)
{
	const struct preference *p1 = v1, *p2 = v2;

	/* Sort by preference_number. */
	if (p1->prefnum < p2->prefnum) return -1;
	if (p1->prefnum > p2->prefnum) return 1;
	/* consider same preference number as equal */
	return 0;
	
}

/* DDS3.22: Save Entry */
static bool save_deo_vote(unsigned int batch_number, 
			  unsigned int paper_index, 
			  struct entry *newentry)
{
	unsigned int i,prefnum;
	const struct preference_set *prefs;
	PGconn *conn = connect_db_host(DATABASE_NAME,SERVER_ADDRESS);
	if (!conn) bailout ("Can't connect to %s at %s\n",
				   DATABASE_NAME,SERVER_ADDRESS);
	prefs = get_vote_in_progress();

	/* Insert preferences from vote in progress*/
	for (i=0; i<prefs->num_preferences; i++) {
		prefnum = prefs->candidates[i].prefnum;
		newentry->preferences[i].prefnum 
			= prefs->candidates[i].prefnum;
		newentry->preferences[i].group_index
			= prefs->candidates[i].group_index;
		newentry->preferences[i].db_candidate_index 
			= prefs->candidates[i].db_candidate_index;
		newentry->e.num_preferences++;
	}
	/* sort them into ascending order*/
	qsort(newentry->preferences, newentry->e.num_preferences, sizeof(*newentry->preferences), cmp_prefnum);

	/* Save the new entry in the <elec>_entry and <elec>_paper database tables */
	
	append_entry(conn, newentry, batch_number, paper_index); 

	PQfinish(conn);
	return true;
}

/* DDS3.22: Confirm Paper */
void confirm_paper(unsigned int pvn)
{
	PGconn *conn;
	struct paper *paper;
	struct entry *newentry, *i,*lasti=NULL;
	unsigned int batch_number, paper_index;
	char *operator_id;
	const struct preference_set *prefs;
	bool equal, save_ok, confirm_save = true;

	operator_id = get_operator_id();
	
	batch_number = get_current_batch_number(); 
	paper_index = get_current_paper_index();

	conn = connect_db_host(DATABASE_NAME, SERVER_ADDRESS);
	assert(conn);
	paper = get_paper(conn, batch_number, paper_index);
	PQfinish(conn);

	/* Count the number of entries already in paper */
	number_of_entries = 0;

	for (i = paper->entries; i; i = i->next) {
		    number_of_entries++;
		    lasti=i;
	}

	/* If more than one entry, need to check if existing entries are 
	   correct or contain uncorrectable errors, i.e. two previous entries match.
	   But if operator is a SUPER, don't perform this check, since the super
	   may need to correct multiple incorrect entries */
	
	if ((strncmp(operator_id,"super",5) !=0) && (number_of_entries > 1)) {
		for (i = paper->entries; i; i = i->next) {
			if ( i != lasti ) {
				equal = compare_entries(lasti, i);
				if (equal) {
					/* Discard new entry */
					confirm_save = false;
					break;
				}
			}
		}
	}
	/* Save new entry */
	if (confirm_save) {
		prefs = get_vote_in_progress();
		newentry = malloc(sizeof(struct entry) 
					+ strlen(operator_id) + 1
					+sizeof(struct preference) 
					* prefs->num_preferences);
		newentry->e.paper_version_num = pvn;
		newentry->e.num_preferences = 0;
		strcpy(newentry->e.operator_id, operator_id);
		save_ok =  save_deo_vote(batch_number, paper_index, newentry);
		if (!save_ok) {
			bailout("Could not save paper - "
				"Internal Error\n");
		}
	}
	update_current_paper_index();

}
