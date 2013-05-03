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

#ifndef VIEWVOTERDIALOG_H
#define VIEWVOTERDIALOG_H

#include "PublicKey.h"

#include "ui_viewvoterdialog.h"
#include "Client.h"
#include "Procedure.h"

class ViewVoterDialog : public QDialog
{
    Q_OBJECT
    
public:
    ViewVoterDialog(Procedure proc, Client* client, QString voter_id, 
                    QWidget* parent = 0);
    
public slots:
    void got_ballot_proof(Client::Error error, QString proof);
    void got_vote(Client::Error error, QString vote);
    void got_num_choices(Client::Error error, int num);
    void got_public_key(Client::Error error, QString pub_key);
    void on_verifyPushButton_clicked();
    
private:
    Ui::ViewVoterDialog ui;
 
    Procedure proc;
    Client* client;
    QString voter_id; 

    adder::Context* context;
    adder::PublicKey* public_key;
    int num_choices;

    int not_done;
};

#endif // VIEWVOTERDIALOG_H
