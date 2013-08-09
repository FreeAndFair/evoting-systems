#ifndef _UPDATE_ENS_SUMMARIES_H
#define _UPDATE_ENS_SUMMARIES_H 
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

/* This file contains global definitions, used throughout EVACS */

#include <libpq-fe.h>
#include <common/batch.h>

extern void update_vote_summary(PGconn *conn, 
				struct normalised_preference *np,
				unsigned int polling_place_code, 
				unsigned int electorate_code);

extern void update_preference_summary(PGconn *conn, 
				      struct preference *p,
				      unsigned int polling_place_code, 
				      unsigned int electorate_code); 

#endif /*  _UPDATE_ENS_SUMMARIES_H */ 
