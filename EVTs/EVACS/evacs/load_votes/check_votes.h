#ifndef _CHECK_VOTES_H
#define _CHECK_VOTES_H
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

#define LOAD1DB_NAME "evacs1"
#define LOAD2DB_NAME "evacs2"

extern struct preference_set get_prefs_for_vote(PGconn *conn,
						unsigned int vote_index);

extern bool check_votes(void);

#endif /*_CHECK_VOTES_H*/
