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
#include <stdbool.h>
#include <assert.h>
#include "cursor.h"

/* Create a mapping for the rotation, collapsed to this number of
   candidates */
static void produce_collapsed_map(const struct rotation *rot,
				  unsigned int map[],
				  unsigned int num_candidates)
{
	unsigned int i,j=0;

	/* get the number of seats from the robson rotation */

	/* run through each robson rotation position
	   adding the value to the map if there is a candidate
	   at that position  
	*/
	for (i = 0; i < rot->size; i++) {
	  /* is there a candidate for this position?   */
	        if (rot->rotations[i] < num_candidates) {
		  /* yes, add it to the map  */
	                map[j]=rot->rotations[i];
	                j++;
	        }
	}
	
}

/* SIPL 2011-06-28 Support split groups.  Comment out the
   previous implementations of these functions, making them
   not available, so that there is no chance that they will
   be used elsewhere in the system. */

// unsigned int translate_dbci_to_sci(unsigned int num_candidates,
// 				   unsigned int db_candidate_index,
// 				   const struct rotation *rot)
// {
// 	unsigned int map[MAX_ELECTORATE_SEATS];
// 	unsigned int i;
// 
// 	assert(num_candidates <= rot->size);
// 	assert(db_candidate_index < rot->size);
// 	assert(db_candidate_index < num_candidates);
// 
// 	produce_collapsed_map(rot, map, num_candidates);
// 
// 	/* Look for the screen candidate index which maps onto this
// 	   db_candidate_index */
// 	for (i = 0; map[i] != db_candidate_index; i++)
// 		assert(i < num_candidates);
// 
// 	return i;
// }

// /* DDS3.2.12: Translate SCI to DBCI */
// unsigned int translate_sci_to_dbci(unsigned int num_candidates,
// 				   unsigned int screen_candidate_index,
// 				   const struct rotation *rot)
// {
// 	unsigned int map[MAX_ELECTORATE_SEATS];
// 	unsigned int i;
// 
// 	assert(screen_candidate_index < num_candidates);
// 
// 	produce_collapsed_map(rot, map, num_candidates);
// 
// 	/* Look for the candidate index which maps onto this
// 	   screen_candidate_index */
// 	for (i = 0; i != map[screen_candidate_index]; i++)
// 		assert(i < num_candidates);
// 
// 	return i;
// }


/* SIPL 2011-06-28 New implementations of these key functions. */

unsigned int translate_group_dbci_to_sci(unsigned int group_index,
				   unsigned int db_candidate_index,
				   const struct rotation *rot)
{
	unsigned int map[MAX_ELECTORATE_SEATS];
	unsigned int i;

	struct ballot_contents *ballot;
	unsigned int physical_column_index;
	/* If the group is split into multiple columns, the
	   sci and dbci values of a candidate _not_ in the
	   first physical column of the group are offset by the
	   total number of candidates in all of the preceding
	   physical columns for the same group.  The variable
	   candidates_offset is used to keep track of that total.
	 */
	unsigned int candidates_offset = 0;

	unsigned int num_candidates;

	/* Skip to the appropriate physical column. */
	ballot = get_ballot_contents();
	physical_column_index =
		ballot->map_group_to_physical_column[group_index];
	while (db_candidate_index >= ballot->num_candidates_in_physical_column[
						physical_column_index]) {
		db_candidate_index = db_candidate_index -
			ballot->num_candidates_in_physical_column[
					      physical_column_index];
		candidates_offset = candidates_offset +
			ballot->num_candidates_in_physical_column[
					      physical_column_index];
		physical_column_index++;
	}
	num_candidates = ballot->num_candidates_in_physical_column[
				physical_column_index];

	assert(num_candidates <= rot->size);
	assert(db_candidate_index < rot->size);
	assert(db_candidate_index < num_candidates);

	produce_collapsed_map(rot, map, num_candidates);

	/* Look for the screen candidate index which maps onto this
	   db_candidate_index */
	for (i = 0; map[i] != db_candidate_index; i++)
		assert(i < num_candidates);

	/* Restore i to the appropriate range of values using
	   candidates_offset. */
	return i + candidates_offset;
}

/* DDS3.2.12: Translate SCI to DBCI */
unsigned int translate_group_sci_to_dbci(unsigned int group_index,
				   unsigned int screen_candidate_index,
				   const struct rotation *rot)
{
	unsigned int map[MAX_ELECTORATE_SEATS];
	unsigned int i;

	struct ballot_contents *ballot;
	unsigned int physical_column_index;
	/* If the group is split into multiple columns, the
	   sci and dbci values of a candidate _not_ in the
	   first physical column of the group are offset by the
	   total number of candidates in all of the preceding
	   physical columns for the same group.  The variable
	   candidates_offset is used to keep track of that total.
	 */
	unsigned int candidates_offset = 0;

	unsigned int num_candidates;

	/* Skip to the appropriate physical column. */
	ballot = get_ballot_contents();
	physical_column_index =
		ballot->map_group_to_physical_column[group_index];
	while (screen_candidate_index >=
	       ballot->num_candidates_in_physical_column[
				physical_column_index]) {
		screen_candidate_index = screen_candidate_index -
			ballot->num_candidates_in_physical_column[
					      physical_column_index];
		candidates_offset = candidates_offset +
			ballot->num_candidates_in_physical_column[
					      physical_column_index];
		physical_column_index++;
	}
	num_candidates = ballot->num_candidates_in_physical_column[
				physical_column_index];

	assert(screen_candidate_index < num_candidates);

	produce_collapsed_map(rot, map, num_candidates);

	/* Look for the candidate index which maps onto this
	   screen_candidate_index */
	for (i = 0; i != map[screen_candidate_index]; i++)
		assert(i < num_candidates);

	/* Restore i to the appropriate range of values using
	   candidates_offset. */
	return i + candidates_offset;
}



/* SIPL 2011-06-28 Please note the hard-coded limit of 7 candidates
   in a column.  Should this function ever be needed again, fix it.
   But this function is not really needed at all, so it has been
   commented out.
 */

// /* Functions below this point are used by the stripped-down client to display
//    the ballot papers during the elections setup */ 
// static void dummy_collapsed_map(const struct rotation *rot,
// 				  unsigned int map[],
// 				  unsigned int num_candidates)
// {
// 	unsigned int i,j=0;
// 
// 	/* get the number of seats from the robson rotation */
// 	struct rotation rot2;
// 
// 	/* use a dummy rotation */
// 	rot2.rotations[0]=0;
// 	rot2.rotations[1]=1;
// 	rot2.rotations[2]=2;
// 	rot2.rotations[3]=3;
// 	rot2.rotations[4]=4;
// 	rot2.rotations[5]=5;
// 	rot2.rotations[6]=6;
// 	rot2.size=7;
// 
// 	/* run through each robson rotation position
// 	   adding the value to the map if there is a candidate
// 	   at that position  
// 	*/
// 	for (i = 0; i < rot2.size; i++) {
// 	  /* is there a candidate for this position?   */
// 	        if (rot2.rotations[i] < num_candidates) {
// 		  /* yes, add it to the map  */
// 	                map[j]=rot2.rotations[i];
// 	                j++;
// 	        }
// 	}
// 	
// }


/* SIPL 2011-06-28 No replacement for this function, as it was not
   used anyway. */

// unsigned int dummy_dbci_to_sci(unsigned int num_candidates,
// 				   unsigned int db_candidate_index,
// 				   const struct rotation *rot)
// {
// 	unsigned int map[MAX_ELECTORATE_SEATS];
// 	unsigned int i;
// 
// 	assert(num_candidates <= rot->size);
// 	assert(db_candidate_index < rot->size);
// 	assert(db_candidate_index < num_candidates);
// 
// 	dummy_collapsed_map(rot, map, num_candidates);
// 
// 	/* Look for the screen candidate index which maps onto this
// 	   db_candidate_index */
// 	for (i = 0; map[i] != db_candidate_index; i++)
// 		assert(i < num_candidates);
// 
// 	return i;
// }

// /* DDS3.2.12: Translate SCI to DBCI */
// unsigned int dummy_sci_to_dbci(unsigned int num_candidates,
// 				   unsigned int screen_candidate_index,
// 				   const struct rotation *rot)
// {
// 	unsigned int map[MAX_ELECTORATE_SEATS];
// 	unsigned int i;
// 
// 	assert(screen_candidate_index < num_candidates);
// 
// 	dummy_collapsed_map(rot, map, num_candidates);
// 
// 	/* Look for the candidate index which maps onto this
// 	   screen_candidate_index */
// 	for (i = 0; i != map[screen_candidate_index]; i++)
// 		assert(i < num_candidates);
// 
// 	return i;
// }
