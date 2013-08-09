#ifndef _GET_ELECTORATE_BALLOT_CONTENTS
#define _GET_ELECTORATE_BALLOT_CONTENTS
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

/* fill a ballot_contents structure with database values */
#include <common/database.h>
#include <common/ballot_contents.h>

extern struct ballot_contents *
get_electorate_ballot_contents(PGconn *conn,
			       unsigned int electorate_code);

#endif /* _GET_ELECTORATE_BALLOT_CONTENTS */
