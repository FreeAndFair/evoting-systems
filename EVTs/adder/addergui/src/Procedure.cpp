/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  AdderGUI - Graphical client for the Adder system.
    Copyright (C) 2006  The Adder Team

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
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

#include <iostream>
#include "Procedure.h"

using namespace std;

Procedure::Procedure(const std::string &id, const std::string &title, 
                     const STAGE &stage, 
                     const int remaining,
                     const int threshold, 
                     const int robustness,
                     const int minchoices,
                     const int maxchoices)
{
    this->id = id;
    this->title = title;
    this->stage = stage;
    this->remaining = remaining;
    this->threshold = threshold;
    this->robustness = robustness;
    this->minchoices = minchoices;
    this->maxchoices = maxchoices;
}

const std::string Procedure::get_stage_desc()
{
    switch (stage) {
    case STAGE_NOTSTARTED:
        return "Not started";
    case STAGE_WAITKEYS:
        return "Authority public key submission";
    case STAGE_WAITPOLYNOMIAL:
        return "Authority polynomial data submission";
    case STAGE_WAITGETPRIVKEYS:
        return "Authority private key storage";
    case STAGE_COMPUTINGPUBKEY: 
        return "Public key computing";
    case STAGE_VOTING:
        return "Voting";
    case STAGE_ADDCIPHER:
        return "Tallying";
    case STAGE_WAITDECRYPT:
        return "Authority decryption";
    case STAGE_DECRYPTING:
        return "Decryption";
    case STAGE_FINISHED:
        return "Finished";
    case STAGE_HALT:
        return "Error";
    case STAGE_NONEXIST:
        return "Procedure does not exist";
    default:
        return "Unknown stage.";
    }
}
