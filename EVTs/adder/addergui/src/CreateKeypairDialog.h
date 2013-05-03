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

#ifndef CREATEKEYPAIRDIALOG_H
#define CREATEKEYPAIRDIALOG_H

#include "PublicKey.h"

#include "ui_createkeypairdialog.h"
#include "Client.h"

class CreateKeypairDialog : public QDialog
{
    Q_OBJECT
    
public:
    CreateKeypairDialog(Client* client, QString proc_id, 
                        QString user_id, QString password, QWidget* parent = 0);
    ~CreateKeypairDialog();
    
private slots:
    void on_createPushButton_clicked();
    void on_submitPushButton_clicked();

    void got_key_constants(Client::Error error, QString key_constants);
    void sent_public_key(Client::Error);
    bool read_pub_key();

private:
    Ui::CreateKeypairDialog ui;

    Client* client;
    QString proc_id;
    adder::PublicKey* master_pub_key;
    adder::PublicKey public_key;
    adder::Context* context;
    QString user_id;
    QString password;
};

#endif // CREATEKEYPAIRDIALOG_H
