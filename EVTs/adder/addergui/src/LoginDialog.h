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

#ifndef LOGINDIALOG_H
#define LOGINDIALOG_H

#include "ui_logindialog.h"
#include "Client.h"

class LoginDialog : public QDialog
{
    Q_OBJECT
    
public:
    LoginDialog(Client* client, QString proc_id, QString* user_id,
                QString* password, QWidget* parent = 0);
    
private slots:
    void on_loginPushButton_clicked();
    void logged_in(Client::Error error, bool is_authority);

private:
    Ui::LoginDialog ui;

    Client* client;
    QString proc_id;
    QString* user_id;
    QString* password;
};

#endif // LOGINDIALOG_H
