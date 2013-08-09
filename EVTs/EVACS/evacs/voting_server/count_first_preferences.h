#ifndef _COUNT_FIRST_PREFERENCES_H
#define _COUNT_FIRST_PREFERENCES_H
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

/* SIPL 2011: Added indication of either pre-poll or polling day 
 *            after electorate names.  This is the new parameter
 *            "qualification".  The possible values are defined in
 *            display_first_preferences.h.
 *            The value is here converted to a string, and
 *            displayed in parentheses after the electorate name.
 */
/* Count the first preferences for each candidate in e, printing results
   to the screen */
void do_count(struct election *e,
	      struct ballot_list *ballots,
	      struct candidate *vacating,
	      const int qualification);

/* These are used by casual vacancy module */
/* Reset count number */
void reset_count(void);

/* Routine to sum all the vote values in a pile, and return the
   truncated total */
unsigned int truncated_vote_sum(struct ballot_list *ballots);

#endif /* _COUNT_FIRST_PREFERENCES_H */



