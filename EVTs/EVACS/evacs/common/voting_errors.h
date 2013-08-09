#ifndef _VOTING_ERRORS_H
#define _VOTING_ERRORS_H
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

/* Define the error codes used by the voting client and server */
enum error
{
	ERR_OK = 0,
	ERR_BARCODE_MISREAD = 1,
	ERR_BARCODE_AUTHENTICATION_FAILED = 2,
	ERR_BARCODE_PP_INCORRECT = 3,
	ERR_BARCODE_USED = 4,
	ERR_BARCODE_MISMATCH = 5,
	ERR_COMMIT_FAILED = 6,
	ERR_RECONSTRUCTION_FAILED = 7,
	ERR_SERVER_UNREACHABLE = 8,
	ERR_SERVER_RESPONSE_BAD = 9,
	ERR_SERVER_INTERNAL = 10,
	ERR_INTERNAL
};
#endif /*_VOTING_ERRORS_H*/
