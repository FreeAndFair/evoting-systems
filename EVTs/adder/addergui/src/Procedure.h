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

#ifndef PROCEDURE_H
#define PROCEDURE_H

#include <string>

#include <QtGui>

class Procedure
{
public:
    enum STAGE {
        STAGE_NOTSTARTED, /**< Procedure has not yet been started. */
        STAGE_WAITKEYS, /**< Waiting for the public keys of the authorities. */
        STAGE_WAITPOLYNOMIAL, /**< Waiting for the authorities to submit their polynomial data. */
        STAGE_WAITGETPRIVKEYS, /**< Waiting for authorities to get their privkey data. */
        STAGE_COMPUTINGPUBKEY, /**< Computing the public key. */
        STAGE_VOTING, /**< Inside the voting process. */
        STAGE_ADDCIPHER, /**< Sums the votes to get the cipher sum. */
        STAGE_WAITDECRYPT, /**< Waiting for the authorities to submit their decryptions. */
        STAGE_DECRYPTING, /**< Waiting for the system to decrypt the result. */
        STAGE_FINISHED, /**< The election is finished and the result has been posted. */
        STAGE_HALT, /**< An error has occurred and the election cannot continue. */
        STAGE_NONEXIST, /**< This procedure does not exist. */
    };
    
    Procedure(const std::string &id, const std::string &title, const STAGE &stage,
              const int remaining,
              const int threshold, const int robustness,
              const int minchoices, const int maxchoices);
    Procedure() {};

    const std::string get_id() { return id; };
    const std::string get_title() { return title; };
    const STAGE get_stage() { return stage; };
    const std::string get_stage_desc();
    const int get_threshold() { return threshold; };
    const int get_robustness() { return robustness; };
    const int get_remaining() { return remaining; };
    const int get_minchoices() { return minchoices; };
    const int get_maxchoices() { return maxchoices; };

    void set_id(const std::string p_id) { id = p_id; };
    void set_title(const std::string p_title) { title = p_title; };
    void set_stage(const STAGE p_stage) { stage = p_stage; };
    void set_threshold(const int p_threshold) { threshold = p_threshold; };
    void set_robustness(const int p_robustness) { robustness = p_robustness; };
    void set_remaining(const int p_remaining) { remaining = p_remaining; };
    void set_minchoices(const int p_minchoices) { minchoices = p_minchoices; };
    void set_maxchoices(const int p_maxchoices) { maxchoices = p_maxchoices; };

private:
    std::string id;
    std::string title;
    STAGE stage;
    int threshold;
    int robustness;
    int remaining;
    int minchoices;
    int maxchoices;
};

#endif /* PROCEDURE_H */
