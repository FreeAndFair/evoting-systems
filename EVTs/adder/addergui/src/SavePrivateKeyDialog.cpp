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

#include "SavePrivateKeyDialog.h"
#include "Client.h"
#include "key_management.h"

#include "PrivateKey.h"

using namespace std;

SavePrivateKeyDialog::SavePrivateKeyDialog(Client* client, Procedure proc,
                                           QString user_id, QString password, QWidget *parent)
    : QDialog(parent), client(client), proc(proc), user_id(user_id), password(password)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    connect(client, SIGNAL(got_private_key_list(Client::Error, 
                                                std::vector<std::string>)),
            this, SLOT(got_private_key_list(Client::Error,
                                            std::vector<std::string>)));

    client->get_private_key_list(proc.get_id().c_str());
}

void SavePrivateKeyDialog::on_savePushButton_clicked()
{
    std::vector<adder::ElgamalCiphertext> key_list;

    for (unsigned int i = 0; i < key_vec.size(); i++) {
        adder::ElgamalCiphertext key;
        key.from_str(key_vec[i]);
        key_list.push_back(key);
    }

    try {
        adder::PrivateKey priv_key = read_private_key(user_id, proc.get_id().c_str(), password);

        adder::PrivateKey final_key = priv_key.get_final_priv_key(key_list);
        write_private_key2(final_key, user_id, proc.get_id().c_str(), password);

        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("Private key saved successfully."));
        accept();
    } catch (...) {
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error saving private key."));
        return;
    }
}

void SavePrivateKeyDialog::got_private_key_list(Client::Error error, 
                                                std::vector<std::string> key_vec)
{
    switch(error) {
    case Client::Badprocedure:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error getting private key information:\n"
                                 "Procedure not found."));
        break;
    case Client::Baduser:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error getting private key information:\n"
                                 "Not authenticated."));
        break;
    case Client::Badstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error getting private key information:\n"
                                 "You may not get private key information\n"
                                 "at this stage."));
        break;
    case Client::Badauthstage:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error getting private key information:\n"
                                 "You have not reached this stage."));
        break;
    case Client::Notauthority:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Error getting private key information:\n"
                                 "You are not an authority."));
        break;
    case Client::OK:
        this->key_vec = key_vec;
        ui.savePushButton->setEnabled(true);
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error getting\n"
                                 "private key information"));
        break;
    }
}
