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

#ifndef SUBMITPARTIALDECRYPTIONDIALOG_H
#define SUBMITPARTIALDECRYPTIONDIALOG_H

#include "Vote.h"

#include "ui_submitpartialdecryptiondialog.h"
#include "Client.h"

class SubmitPartialDecryptionDialog : public QDialog
{
    Q_OBJECT
    
public:
    SubmitPartialDecryptionDialog(Client* client, Procedure proc, 
                                  QString user_id, QString password, 
                                  QWidget* parent = 0);
    
private slots:
    void on_submitPushButton_clicked();
    void got_cipher_sum(Client::Error error, QString sum);
    void got_num_votes(Client::Error error, int num);
    void sent_sum(Client::Error error);

private:
    Ui::SubmitPartialDecryptionDialog ui;

    Client* client;
    Procedure proc;
    QString user_id;
    QString password;

    int num_votes;
    adder::Vote* cipher_sum;
    
    int not_done; /* Decrement this after receiving each piece of 
                     necessary information.  When 0, we enable the 
                     button. */
};

#endif // SUBMITPARTIALDECRYPTIONDIALOG_H
