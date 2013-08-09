#ifndef BATCH_EDIT_2_H
#define BATCH_EDIT_2_H
/*
   This file is (C) copyright 2001-2007 Software Improvements, Pty Ltd
*/

/*
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

#define LOG_FILE_DIR "/tmp/"

extern FILE *open_log_file(const char *file_name);

extern void close_log_file(void);

extern void delete_duplicate_paper(      PGconn       *conn,
                                   const unsigned int  batch_number,
                                   const unsigned int  electorate_code);

extern void insert_paper(      PGconn       *conn,
                         const unsigned int  batch_number);

extern void append_paper(      PGconn       *conn,
                         const unsigned int  batch_number);

extern bool check_operator_ids_ok (      PGconn       *conn,
                                   const unsigned int  batch_number,
                                   const char         *electorate_name,
                                   const char         *committing_operator);

extern unsigned int get_max_entry_index_of (      PGconn       *conn,
                                            const unsigned int  batch_number,
                                            const unsigned int  paper_id,
                                            const char         *electorate_name);

#endif /* BATCH_EDIT_2_H */
