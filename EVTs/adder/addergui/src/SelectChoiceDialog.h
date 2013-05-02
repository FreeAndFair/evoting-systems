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

#ifndef SELECTCHOICEDIALOG_H
#define SELECTCHOICEDIALOG_H

#include "PublicKey.h"

#include "ui_selectchoicedialog.h"
#include "Client.h"

class SelectChoiceDialog : public QDialog
{
    Q_OBJECT
    
public:
    SelectChoiceDialog(Client* client, Procedure proc, 
                       QString user_id, QWidget* parent = 0);
    
private slots:
    void got_description(QString description);
    void got_choices(std::vector<QString> choices_vec);
    void got_public_key(Client::Error error, QString key);
    void on_submitPushButton_clicked();
    void sent_vote(Client::Error);

private:
    Ui::SelectChoiceDialog ui;

    Client* client;
    Procedure proc;
    QString user_id;
    adder::PublicKey* public_key;

    QProgressDialog* progress;
};

#endif // SELECTCHOICEDIALOG_H
