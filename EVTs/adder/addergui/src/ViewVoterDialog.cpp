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

#include <QtGui>

#include <iostream>
#include <string>

#include "PublicKey.h"
#include "Vote.h"
#include "VoteProof.h"

#include "ViewVoterDialog.h"
#include "Client.h"
#include "Procedure.h"

using namespace std;

ViewVoterDialog::ViewVoterDialog(Procedure proc, Client* client, 
                                 QString voter_id, QWidget *parent)
    : QDialog(parent), proc(proc), voter_id(voter_id), client(client)
{
    setAttribute(Qt::WA_DeleteOnClose);

    not_done = 4;

    connect(client, SIGNAL(got_ballot_proof(Client::Error, QString)),
            this, SLOT(got_ballot_proof(Client::Error, QString)));

    connect(client, SIGNAL(got_vote(Client::Error, QString)),
            this, SLOT(got_vote(Client::Error, QString)));

    connect(client, SIGNAL(got_num_choices(Client::Error, int)),
            this, SLOT(got_num_choices(Client::Error, int)));
    
    connect(client, SIGNAL(got_public_key(Client::Error, QString)),
            this, SLOT(got_public_key(Client::Error, QString)));

    client->get_ballot_proof(proc.get_id().c_str(), voter_id);
    client->get_vote(proc.get_id().c_str(), voter_id);
    client->get_num_choices(proc.get_id().c_str());
    client->get_public_key(proc.get_id().c_str());

    ui.setupUi(this);
}

void ViewVoterDialog::got_ballot_proof(Client::Error error, QString proof)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Procedure does not exist."));
        break;
    case Client::Novote:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Vote not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("User not found."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Voting has not yet begun."));
        break;
    case Client::OK:    
        ui.proofTextBrowser->insertPlainText(proof);

        not_done--;
        if (!not_done) {
            ui.verifyPushButton->setEnabled(true);
        }

        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting ballot proof."));
    }
}

void ViewVoterDialog::got_vote(Client::Error error, QString vote)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Procedure does not exist."));
        break;
    case Client::Novote:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Vote not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("User not found."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Voting has not yet begun."));
        break;
    case Client::OK:    
        ui.voteTextBrowser->insertPlainText(vote);

        not_done--;
        if (!not_done) {
            ui.verifyPushButton->setEnabled(true);
        }

        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting vote."));
    }
}

void ViewVoterDialog::got_num_choices(Client::Error error, int num)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Procedure does not exist."));
        break;
    case Client::OK:    
        num_choices = num;

        not_done--;
        if (!not_done) {
            ui.verifyPushButton->setEnabled(true);
        }

        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting vote."));
    }
}

void ViewVoterDialog::got_public_key(Client::Error error, QString key)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Procedure does not exist."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Public key has not yet been created."));
        break;
    case Client::OK:    
        context = new adder::Context(true);
        public_key = new adder::PublicKey(context);
        public_key->from_str(key.toStdString());

        not_done--;
        if (!not_done) {
            ui.verifyPushButton->setEnabled(true);
        }

        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting vote."));
    }
}

void ViewVoterDialog::on_verifyPushButton_clicked()
{
    adder::VoteProof proof;
    adder::Vote vote;

    proof.from_str(ui.proofTextBrowser->toPlainText().toStdString());
    vote.from_str(ui.voteTextBrowser->toPlainText().toStdString());
    
    bool valid = proof.verify(vote, *public_key, 
                              proc.get_minchoices(),
							  proc.get_maxchoices());
    
    if (valid) {
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Proof is valid."));
    } else {
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Proof is invalid."));
    }
}
