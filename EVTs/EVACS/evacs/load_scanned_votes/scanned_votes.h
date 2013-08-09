#ifndef _SCANNED_VOTES_H
#define _SCANNED_VOTES_H
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


/* This file contains definitions for scanned votes */

#include <common/evacs.h>

/* Scanned votes are loaded into a temporary database
   with this name. */
#define LOADDB_NAME "evacs1"


extern void get_scanned_prefs_for_entry(struct preference preferences[],
                                        unsigned int      *num_preferences,
                                        char              *preference_list);


extern void normalize_scanned_prefs(struct preference  p_out[],
                                    unsigned int      *num_prefs_out,
                                    struct preference  p_in[],
                                    unsigned int       num_prefs_in);

extern void pack_scanned_prefs(char              *preference_list_out,
                               struct preference preferences_in[],
                               unsigned int      num_preferences_in);


#endif /* _SCANNED_VOTES_H */
