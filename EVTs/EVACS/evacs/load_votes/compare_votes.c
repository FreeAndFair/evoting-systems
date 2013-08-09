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
#include <string.h>
#include <common/evacs.h>
#include "compare_votes.h"

/* DDS3.4: Compare Votes */
bool compare_votes(struct vote *vote1, struct vote *vote2)
{

	if (vote1->batch_number != vote2->batch_number ||
	    vote1->paper_version != vote2->paper_version ||
	    strcmp(vote1->preference_list,vote2->preference_list))
		return false;

	return true;

}
	      
			    
			    

			   
				
