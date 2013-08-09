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
#include <stdlib.h>
#include <string.h>
#include <common/database.h>
#include <common/evacs.h>
/*#include <common/safe.h>*/
#include "hare_clark.h"
#include "fetch.h"
#include "report.h"
#include "ballot_iterators.h"
#include "candidate_iterators.h"
#include "count.h"

static struct electorate *prompt_for_electorate(PGconn *conn)
{
	char *name;
	struct electorate *elec;

	do {
		printf("Please enter the electorate name to count: ");
		name = fgets_malloc(stdin);
		elec = fetch_electorate(conn, name);
		if (!elec)
			printf("Electorate `%s' not found!\n", name);
		free(name);
	} while (!elec);

	return elec;
}


static bool free_piles(struct candidate *cand, void *unused)
{
	unsigned int i;

	for (i = 0; i < MAX_COUNTS; i++)
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


int main(int argc, char *argv[])
{
	struct ballot_list *ballots;
	PGconn *conn;
	struct election e;
        char *election_name,*election_date,*election_title;
        /* What to insert between election name and date to
           give the title to print on scrutiny sheets */
        static char election_title_joiner[] = " - ";

	/* Get the information we need */
	conn = connect_db(DATABASE_NAME);
	if (conn == NULL) bailout("Can't connect to database:%s\n",
				   DATABASE_NAME);

        /* Get name and date of election */
        /* master_data (election_name, election_date) */
        election_name = SQL_singleton(conn,
                                      "SELECT election_name "
                                      "FROM master_data;");
        if (election_name == NULL)
          bailout("Can't get election name from database.\n");
        election_date = SQL_singleton(conn,
                                      "SELECT election_date "
                                      "FROM master_data;");
        if (election_date == NULL)
          bailout("Can't get election date from database.\n");

        /* Now put the election title together;
           title = election_name + election_title_joiner + election_date */
        election_title = malloc(sizeof(char) *
                                (strlen(election_name) +
                                 strlen(election_title_joiner) +
                                 strlen(election_date) +
                                 1)); /* add one for NULL at end */
        if (election_title == NULL)
          bailout("Ran out of memory while determining election title.\n");

        strcpy(election_title,election_name);
        strcat(election_title,election_title_joiner);
        strcat(election_title,election_date);

	e.electorate = prompt_for_electorate(conn);
	e.num_groups = fetch_groups(conn, e.electorate, e.groups);
	e.candidates = fetch_candidates(conn, e.electorate, e.groups);
	fprintf(stderr,"Fetching Ballots:\t");
	ballots = fetch_ballots(conn, e.electorate);

        /* 2008-07-29 Abort if there are no ballots to count. */
        if (ballots == NULL) {
          fprintf(stderr,"\nThere are no ballots to be counted "
                  "for this electorate.\n");
          return -1;
        }

  
	/* Start the reporting for a regular Hare Clark count*/
	report_start(&e, NULL);

	do_count(&e, ballots, NULL);

	/* We've finished! */
	fprintf(stderr,"\nFinished Count; Cleaning up\n");
	report_end(get_count_number(), election_title);

	/* free allocated memory */
	for_each_candidate(e.candidates, &free_candidate, NULL);
	for_each_candidate(e.candidates, &free_piles, NULL);
	free_group_names(e.groups, e.num_groups);
	free_cand_list(e.candidates);
	free_electorates(e.electorate);

        free(election_name);
        free(election_date);
        free(election_title);

	PQfinish(conn);
	return 0;
}








