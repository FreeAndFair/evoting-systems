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
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>
#include <common/evacs.h>
#include <common/database.h>

#include "find_errors.h"

/* corresponding error descriptions */
static char *entry_error_string[] = {
	(char *)"Ignord",
	(char *)"Unentd",
	(char *)"Keystr",
	(char *)"Inform",
	(char *)"Miss #",
	(char *)"Dupl #",
	(char *)"Fixed ",
	(char *)"  OK  ",
	(char *)"InvApp"
};

extern char *get_error_string(enum entry_error error_code) {
	return entry_error_string[error_code];
}

extern  bool compare_entry(const struct entry *e1, const struct entry *e2);
extern  const struct entry *last_entry(const struct entry *i);
extern  const struct entry *get_entry_index(const struct entry *i, unsigned int index);

static int comp_pref(const void *v1, const void *v2)
{
	const struct preference *p1 = v1, *p2 = v2;

	/* Sort first by group index. */
	if (p1->group_index < p2->group_index) return -1;
	if (p1->group_index > p2->group_index) return 1;

	/* Group indices are equal.  Differentiate by candidate. */
	assert(p1->db_candidate_index != p2->db_candidate_index);
	if (p1->db_candidate_index < p2->db_candidate_index) return -1;
	return 1;
}

extern bool compare_entry(const struct entry *e1, const struct entry *e2)
{
	unsigned int i;
	struct preference *p1, *p2;

	/* Number of preferences must be the same, as must PVN */
	if (e1->e.num_preferences != e2->e.num_preferences) return false;
	if (e1->e.paper_version_num != e2->e.paper_version_num) return false;
	
	/* Preferences need not be entered in same order.  Sort them */
	p1 = malloc(2*e1->e.num_preferences*sizeof(*p1));
	p2 = p1 + e1->e.num_preferences;
	memcpy(p1, e1->preferences, e1->e.num_preferences*sizeof(*p1));
	memcpy(p2, e2->preferences, e2->e.num_preferences*sizeof(*p2));

	qsort(p1, e1->e.num_preferences, sizeof(*p1), comp_pref);
	qsort(p2, e2->e.num_preferences, sizeof(*p2), comp_pref);

	for (i = 0; i < e1->e.num_preferences; i++) {
		/* Group index, candidate index and prefnum must agree */
		if (p1[i].group_index != p2[i].group_index
		    || p1[i].db_candidate_index != p2[i].db_candidate_index
		    || p1[i].prefnum != p2[i].prefnum) {
			free(p1);
			return false;
		}
	}

	/* All identical */
	free(p1);
	return true;
}

/* Count number of occurrences of this preference number */
static unsigned int num_prefnums(const struct entry *entry,
				 unsigned int prefnum)
{
	unsigned int i, ret;
	for (i = 0, ret = 0; i < entry->e.num_preferences; i++)
		if (entry->preferences[i].prefnum == prefnum)
			ret++;

	return ret;
}

/* Return true if any numbers are missing */
static bool missing_numbers(const struct entry *entry)
{
	unsigned int i;

	/* A number is "missing" if there are gaps in the preference
           numbers: ie. there exists some preference number not equal
           to one for which the previous preference number is not
           present */
	for (i = 0; i < entry->e.num_preferences; i++) {
		unsigned int prefnum;

		prefnum = entry->preferences[i].prefnum;
		if (prefnum != 1 && num_prefnums(entry, prefnum-1) == 0)
			return true;
	}
	return false;
}
 
/* Return true if any numbers are duplicated */
static bool duplicate_numbers(const struct entry *entry)
{
	unsigned int i;

	/* A number is duplicated if it occurs more than once. */
	for (i = 0; i < entry->e.num_preferences; i++)
		if (num_prefnums(entry, entry->preferences[i].prefnum) > 1)
			return true;

	return false;
}

/* Return the last entry in a chain */
extern const struct entry *last_entry(const struct entry *i)
{
	while (i->next)
		i = i->next;

	return i;
}

extern const struct entry *get_entry_index(const struct entry *i, unsigned int index)
{
	struct entry  *tmp,*ret=NULL;

	for (tmp = (struct entry *) i; tmp; tmp=tmp->next) {
		if (tmp->e.index == index) {
			ret=tmp;
			continue;
		}
	}
	return ret;
}

/* DDS 3.6: Compare Entries */
bool compare_entries(const struct entry *head,
		     const struct entry *entry)
{
	while (head) {
		/* Skip over the identical entry */
		if (head != entry) {
			if (compare_entry(head, entry))
				return true;
		}
		head = head->next;
	}
	return false;
}


extern int match_active_entries(PGconn *conn,
			 char *electorate_name,
			 int paper_id) 
{
	int entry_id1=0, entry_id2=0, ret=0;
	struct entry *head = get_entries_for_paper(conn,
						   paper_id,
						   electorate_name);
	struct entry *latest = (struct entry *) last_entry(head);
	struct entry *active1, *active2;
	PGresult *result;
	bool b1=false, b2=false;

	/* retrieve active entries */
	result = SQL_query(conn,
			   "SELECT entry_id1,entry_id2 FROM %s_paper WHERE id = %u;",
			   electorate_name, paper_id
		);
	
	if (PQntuples(result) > 0 ) { 
		entry_id1 = atoi(PQgetvalue(result,0,0));
		entry_id2 = atoi(PQgetvalue(result,0,1));			
	} 

	PQclear(result);
	
	if (entry_id1 > 0) {
		active1=(struct entry *) get_entry_index(head,entry_id1);
		b1=compare_entry(latest,active1);
	}
	
	
	if (entry_id2 > 0) {
		active2=(struct entry *) get_entry_index(head,entry_id2);
		b2=compare_entry(latest,active2);
	}
	
	/* figure out return code */
	if (   b1 &&   b2 ) ret = 3; /* both active entries match    */
	if ( ! b1 &&   b2 ) ret = 2; /* match on active entry 2      */
	if (   b1 && ! b2 ) ret = 1; /* match on active entry 1      */
	if ( ! b1 && ! b2 ) ret = 0; /* neither active entries match */

	free(head);
	return ret;
}

/* DDS 3.6: Find Errors in Entry */
static struct entry_with_error *find_errors_in_entry(const struct entry *head,
						     const struct entry *entry,
						     unsigned int paper_index,
						     unsigned int batch_size)
{
	struct entry_with_error *ewe;

	ewe = malloc(sizeof(*ewe)
		     + sizeof(ewe->preferences[0])*entry->e.num_preferences);

	/* Copy preferences */
	ewe->e = entry->e;
	memcpy(ewe->preferences, entry->preferences,
	       sizeof(ewe->preferences[0]) * ewe->e.num_preferences);

	/* Judge error */
	if (paper_index > batch_size)
		/* Paper index is one-based */
		ewe->error_code = ENTRY_ERR_IGNORED;
	else if (head->next == NULL)
		/* Only one entry */
		ewe->error_code = ENTRY_ERR_UNENTERED;
	else if (entry->next == NULL
		 && !compare_entries(head, entry))
		/* This is the last entry, and matches no previous ones */
		ewe->error_code = ENTRY_ERR_KEYSTROKE;
	else if (entry->next != NULL
		 && !compare_entry(last_entry(head), entry))
		/* Not the last entry, and does not match last entry */
		ewe->error_code = ENTRY_ERR_KEYSTROKE;
	else if (num_prefnums(entry, 1) != 1)
		/* Not a single "1" preference */
		ewe->error_code = ENTRY_ERR_INFORMAL;
	else if (missing_numbers(entry))
		/* Missing preference numbers */
		ewe->error_code = ENTRY_ERR_MISSING_NUM;
	else if (duplicate_numbers(entry))
		/* Duplicated preference numbers */
		ewe->error_code = ENTRY_ERR_DUPLICATED_NUM;
	else if (head->next->next != NULL)
		/* More than two entries */
		ewe->error_code = ENTRY_ERR_CORRECTED;
	else 
		ewe->error_code = ENTRY_ERR_CORRECT;

	return ewe;
}

/* DDS 3.6: Find Errors in Paper */
struct paper_with_error find_errors_in_paper(PGconn *conn,
						    const struct paper *paper,
						    unsigned int paper_index,
						    unsigned int batch_number,
						    unsigned int batch_size,
						const char *electorate_name)
{
	struct paper_with_error pwe;
	const struct entry *i;
	struct entry_with_error *ewe = NULL;
	int active_entry1;
	int active_entry2;
	const struct entry *ae1 = NULL;
	const struct entry *ae2 = NULL;

	assert(paper->entries);

	/* Transfer core information */
	pwe.p = paper->p;

	/* Prepend the translated entries one at a time */
	pwe.entries = NULL;
	for (i = paper->entries; i; i = i->next) {
		ewe = find_errors_in_entry(paper->entries,
					   i,
					   paper_index,
					   batch_size);
		ewe->next = pwe.entries;
		pwe.entries = ewe;
	}

	/* Our error status == that of last entry */
	pwe.error_code = ewe->error_code;

        /*
          Determine the error associated with the two active entries.
          This is because where an insetion, deletion, or an appending
          action is done a complete copy (excepte a deleted entry) of
          and entry is made.
          This means that some of the error codes calculated above are
          incorrect as they could be between copies of the same paper
          entry.
          The most important error code is the last one determined.
          The following code examines the active entries and sets
          the last error code based on that comparsion.
        */

        get_active_entries(conn,
                           electorate_name,
                           batch_number,
                           paper_index,
                           &active_entry1,
                           &active_entry2);

        if (active_entry1 > 0)
          ae1 = get_entry_index(paper->entries, active_entry1);

        if (active_entry2 > 0)
          ae2 = get_entry_index(paper->entries, active_entry2);

        if (ae1 && ae2) {
          if (!compare_entry(ae1, ae2)) ewe->error_code = ENTRY_ERR_KEYSTROKE;

          pwe.error_code = ewe->error_code;

        } else if (ae1 || ae2) {

          /* If there is only one active entry, then ensure that an error
             is flagged. */

          ewe->error_code = ENTRY_ERR_UNENTERED;
          pwe.error_code  = ewe->error_code;
        }

	return pwe;
}

struct batch_with_error *find_errors_in_batch(PGconn *conn,
                                              const struct batch *batch,
                                              const char *electorate_name)
{
	struct batch_with_error *bwe;
	unsigned int i;

	/* Allocate enough space for the papers */
	bwe = malloc(sizeof(*bwe)
		     + batch->b.num_papers*sizeof(bwe->papers[0]));

	/* Transfer information across */
	bwe->b = batch->b;
	for (i = 0; i < bwe->b.num_papers; i++)
		bwe->papers[i] = find_errors_in_paper(conn,
                                                      &batch->papers[i],
						      i+1,
                                                      bwe->b.batch_number,
						      bwe->b.batch_size,
                                                      electorate_name);
	return bwe;
}

void free_batch_with_error(struct batch_with_error *bwe)
{
	unsigned int i;

	/* For every paper, free linked list of entries */
	for (i = 0; i < bwe->b.num_papers; i++) {
		while (bwe->papers[i].entries) {
			struct entry_with_error *next;

			next = bwe->papers[i].entries->next;
			free(bwe->papers[i].entries);
			bwe->papers[i].entries = next;
		}
	}

	free(bwe);
}
