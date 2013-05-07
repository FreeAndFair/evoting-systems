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
#include "PrivateKey.h"
#include "Context.h"
#include "exceptions.h"

#include "CreateKeypairDialog.h"
#include "Client.h"

#include "key_management.h"

using namespace std;

CreateKeypairDialog::CreateKeypairDialog(Client* client, QString proc_id, 
                                         QString user_id, QString password, 
                                         QWidget *parent)
    : QDialog(parent), client(client), proc_id(proc_id), user_id(user_id), 
      password(password)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    context = new adder::Context(true);
    
    if (read_pub_key()) {
        ui.submitPushButton->setEnabled(true);
    }

    connect(client, SIGNAL(got_key_constants(Client::Error, QString)),
            this, SLOT(got_key_constants(Client::Error, QString)));

    connect(client, SIGNAL(sent_public_key(Client::Error)),
            this, SLOT(sent_public_key(Client::Error)));

    client->get_key_constants(proc_id);
}

CreateKeypairDialog::~CreateKeypairDialog()
{
    delete context;
}

bool CreateKeypairDialog::read_pub_key()
{
    try {
        public_key = read_public_key(user_id,
                                     proc_id,
                                     context);
    } catch (...) {
        return false;
    }
}

void CreateKeypairDialog::on_createPushButton_clicked()
{
    if (!create_keypair(user_id, proc_id, 
                        *master_pub_key, password)) {
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error creating keypair."));
    } else {
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Keypair created successfully."));

        if (read_pub_key()) {
            ui.submitPushButton->setEnabled(true);
        }
    }
}

void CreateKeypairDialog::on_submitPushButton_clicked()
{
    adder::Context context(true);
    
    try {
        adder::PublicKey key = read_public_key(user_id,
                                               proc_id,
                                               &context);

        QString pub_key_str(key.str().c_str());
        client->send_public_key(pub_key_str, proc_id);
    } catch (Failed) {
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Invalid or non-existant public key."));
    }
}

void CreateKeypairDialog::got_key_constants(Client::Error error, QString key)
{
    adder::Context context(true);
   
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Procedure does not exist."));
        break;
    case Client::Nokey:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Key constants not found."));
        break;
    case Client::OK:    
        master_pub_key = new adder::PublicKey(&context);
        
        try {
            master_pub_key->from_str(key.toStdString());
            ui.createPushButton->setEnabled(true);
        } catch (adder::Invalid_key) {
            QMessageBox::critical(this, tr("AdderGUI"),
                                  tr("Invalid public key."));
        }
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting key constants."));
    }
}

void CreateKeypairDialog::sent_public_key(Client::Error error)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting public key:\n"
                                 "Procedure not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting public key:\n"
                                 "Not authenticated."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting public key:\n"
                                 "You may not submit a public key\n"
                                 "at this stage."));
        break;
    case Client::Duplicate:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting public key:\n"
                                 "You have already submitted a\n"
                                 "public key."));
        break;
    case Client::Badkey:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting public key:\n"
                                 "This key is malformed."));
        break;
    case Client::OK:
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Public key submitted successfully."));
        accept();
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error submitting public key:\n"
                                 "Procedure not found."));
        break;
    }
}
