#ifndef _BATCH_ENTRY_H
#define _BATCH_ENTRY_H
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


#include <common/evacs.h>
#include <common/batch.h>
#include <common/batch_history.h>
/*#include <common/safe.h>*/
#include <common/database.h>
#include <common/find_errors.h>

#define MAX_INT_LINE_LENGTH 100

/* prototype definitions */
extern void batch_entry(void);
extern void wait_for_reset(void);

#endif  /* _BATCH_ENTRY_H */


