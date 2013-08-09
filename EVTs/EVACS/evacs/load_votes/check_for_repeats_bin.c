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
#include <common/database.h>
#include <common/evacs.h>
#include "check_for_repeats.h"
#include "check_votes.h"
#include "compare_votes.h"

int main(void) {

	bool ret;
	
	ret = check_for_repeats();
	/* if something else fails, we exit with 01, so we can't
	   return 1 on success */
	if (ret)
		exit(1);
        else
		exit(0);

}
