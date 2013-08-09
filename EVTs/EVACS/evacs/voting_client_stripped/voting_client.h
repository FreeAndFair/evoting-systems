#ifndef _VOTING_CLIENT_H
#define _VOTING_CLIENT_H
/* This file is (C) copyright 2001-2004 Software Improvements, Pty Ltd */

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

/* Common routines and definitions for Voting Client */
#include <common/evacs.h>
#include <common/voting_errors.h>
#include <common/voter_electorate.h>

#define IMAGE_BASE "/images/messages/"
#define AUDIO_BASE "/audio/"
#define NUMBER_BASE "/images/%u/numbers/"
#define CANDIDATE_BASE "/images/electorates/"
#define GROUP_BASE "/images/electorates/"

/* Number of Languages must be even. If not, fix welcome_screen */
#define NUM_OF_LANGUAGES 12

#endif /*_VOTING_CLIENT_H*/
