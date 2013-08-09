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


/* Process scanned votes */

/* For malloc() */
#include <stdlib.h>
/* For memset() */
#include <string.h>

#include <common/evacs.h>
#include <common/batch.h>
#include "scanned_votes.h"





/* load the entry structure pointed to by entry with preference data*/
void get_scanned_prefs_for_entry(struct preference preferences[],
                                 unsigned int      *num_preferences,
                                 char              *preference_list)
{
  unsigned int  i;
  char         *pref_ptr;

  /* Decode preference list into memory structure */
  for (i = 0, pref_ptr = preference_list;
       *pref_ptr;
       i++, pref_ptr += DIGITS_PER_PREF*sizeof(char)) {
    sscanf(pref_ptr, (const char *)"%2u%2u%2u",
           &preferences[i].prefnum,
           &preferences[i].group_index,
           &preferences[i].db_candidate_index);
  }
  *num_preferences = i;
} //get_scanned_prefs_for_entry


void normalize_scanned_prefs(struct preference  p_out[],
                             unsigned int      *num_prefs_out,
                             struct preference  p_in[],
                             unsigned int       num_prefs_in)
/*
  Returns a list of preferences which have Preference Indexes in ascending
  order starting from one, with no missing numbers.
*/
{
  unsigned int prefnum = 1,
    i,
    j       = 0,
    count;
  
  while (1) {
    /* Count number of time prefnum appears */
    count = 0;
    for (i = 0; i < num_prefs_in; i++)
      if (p_in[i].prefnum == prefnum) {
        j = i;
        count++;
      }

    /* If only once - then copy across */
    if (count == 1 ) {
      p_out[prefnum-1].prefnum            = p_in[j].prefnum;
      p_out[prefnum-1].group_index        = p_in[j].group_index;
      p_out[prefnum-1].db_candidate_index = p_in[j].db_candidate_index;
      prefnum++;
      
    } else /* zero or more than one - exit loop */
      break;
  }

  *num_prefs_out = prefnum - 1;
}

void pack_scanned_prefs(char              *preference_list_out,
                        struct preference preferences_in[],
                        unsigned int      num_preferences_in)
{
  unsigned int i;
  char *pref_ptr;

  *preference_list_out = '\0';
  
  for (i = 0,pref_ptr=preference_list_out;
       i < num_preferences_in;
       i++,pref_ptr += (sizeof(char)*(DIGITS_PER_PREF)))
    sprintf(pref_ptr,
            "%02u%02u%02u",
            preferences_in[i].prefnum,
            preferences_in[i].group_index,
            preferences_in[i].db_candidate_index);
}
