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

#include "Vote.h"

#include "SubmitPartialDecryptionDialog.h"
#include "Client.h"

#include "key_management.h"

using namespace std;

SubmitPartialDecryptionDialog::SubmitPartialDecryptionDialog
(Client* client, Procedure proc, 
 QString user_id, QString password,
 QWidget *parent)
    : QDialog(parent), client(client), proc(proc), user_id(user_id), password(password)
{
    setAttribute(Qt::WA_DeleteOnClose);

    not_done = 2; // There are two things to get before enabled the submit button.

    connect(client, SIGNAL(got_cipher_sum(Client::Error, QString)),
            this, SLOT(got_cipher_sum(Client::Error, QString)));
    connect(client, SIGNAL(got_num_votes(Client::Error, int)),
            this, SLOT(got_num_votes(Client::Error, int)));
    connect(client, SIGNAL(sent_sum(Client::Error)),
            this, SLOT(sent_sum(Client::Error)));
    
    client->get_cipher_sum(proc.get_id().c_str());
    client->get_num_votes(proc.get_id().c_str());

    ui.setupUi(this);
}

void SubmitPartialDecryptionDialog::got_cipher_sum(Client::Error, 
                                                   QString sum)
{
    cipher_sum = new adder::Vote;

    try {
        cipher_sum->from_str(sum.toStdString());
        not_done--;
        if (!not_done) {
            ui.submitPushButton->setEnabled(true);
        }
    } catch (...) {
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown problem getting encrypted sum."));
    }
}

void SubmitPartialDecryptionDialog::got_num_votes(Client::Error,
                                                  int num)
{
    num_votes = num;
    not_done--;

    if (!not_done) {
        ui.submitPushButton->setEnabled(true);
    }
}

void SubmitPartialDecryptionDialog::on_submitPushButton_clicked()
{
    vector<adder::Integer> decryption = decrypt_sum(user_id,
                                                    proc.get_id().c_str(),
                                                    *cipher_sum,
                                                    password);

    for (int i = 0; i < decryption.size(); i++) {
        cout << "int: " << decryption[i].str() << endl;
    }

    client->send_sum(decryption, proc.get_id().c_str());
}

void SubmitPartialDecryptionDialog::sent_sum(Client::Error error)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting decryption:\n"
                                 "Procedure not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting decryption:\n"
                                 "Not authenticated."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting decryption:\n"
                                 "You may not submit a decryption\n"
                                 "at this stage."));
        break;
    case Client::Duplicate:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting decryption:\n"
                                 "You have already submitted a\n"
                                 "decryption."));
        break;
    case Client::Badauthstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting decryption:\n"
                                 "You are not allowed to participate\n"
                                 "at this stage."));
    case Client::OK:
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Decryption submitted successfully."));
        accept();
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting decryption:\n"
                                 "Procedure not found."));
        break;
    }
}
