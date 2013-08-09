#ifndef _COMMIT_VOTE_H
#define _COMMIT_VOTE_H
/* This file is (C) copyright 2001 Software Improvements, Pty Ltd.
   
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
/* This file contains the definitions for the commit_vote CGI */

/* We define our own bailout routine which returns an error to the
   client */
extern void cgi_bailout(const char *fmt, ...)
__attribute__((noreturn, format(printf,1,2)));

#endif /*_COMMIT_VOTE_H*/
