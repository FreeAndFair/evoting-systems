#ifndef _BATCH_HISTORY_H
#define _BATCH_HISTORY_H
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

/* This file contains definitions for batches */
#include <string.h>
#include <stdlib.h>
#include <common/database.h>
#include <common/voter_electorate.h>
#include <common/batch.h>
#include <common/find_errors.h>
/* for 'get_operator_id()' */
#include <data_entry/confirm_paper.h>
#include <data_correction/batch_edit.h>

#include <stdbool.h>
#include <libpq-fe.h>
#include "evacs.h"



extern void report_batch_history(PGconn *conn,
				 unsigned int batch_number);


#endif /* _BATCH_HISTORY_H */










