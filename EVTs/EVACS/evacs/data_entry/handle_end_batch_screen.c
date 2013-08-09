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
#include <stdio.h>
#include <stdlib.h>
#include <voting_client/image.h>
#include <common/batch.h>
#include "handle_end_batch_screen.h"
#include "interpret_deo_keystroke.h"



/* DDS3.24: Handle END BATCH Screen */
bool handle_end_batch_screen(void)
{
	unsigned int batch_number;
	char *buf, c;
	unsigned int key;


	batch_number = get_current_batch_number();
	while (1) {
		printf("\nAre you sure you have completed entering Batch: %u? "
	       "[y/n ENTER]", batch_number);
		fflush(stdin);
		buf = fgets_malloc(stdin);
		c =  (char) buf[0];
		key = (unsigned int) c;
		free(buf); 
		if (key == DEO_END_BATCH_KEYSTROKE_Y || 
		    key == DEO_END_BATCH_KEYSTROKE_y || 
		    key ==  DEO_END_BATCH_KEYSTROKE_ENTER) { 
			return true;
		} else if (key == DEO_END_BATCH_KEYSTROKE_n || 
			   key == DEO_END_BATCH_KEYSTROKE_N) { 
			return false;
		}
	}
}
	
