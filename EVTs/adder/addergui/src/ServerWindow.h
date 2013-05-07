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

#ifndef SERVERWINDOW_H
#define SERVERWINDOW_H

#include <vector>

#include "ui_serverwindow.h"
#include "ui_aboutdialog.h"

#include "Client.h"
#include "Procedure.h"
#include "ConsoleDialog.h"

class ServerWindow : public QMainWindow
{
    Q_OBJECT
    
public:
    ServerWindow(QWidget* parent = 0);
    QSize sizeHint() const;

signals:
    void request_version();
    
private slots:
    void open_connect_dialog();
    void open_about_dialog();
    void open_create_proc_wizard();
    void client_disconnect();
    void client_connect();
    void refresh_procedure_list(std::vector<Procedure> procedure_vec);
    void create_procedure(Client::Error procedure_error);
    void delete_procedure(Client::Error procedure_error);
    void start_procedure(Client::Error procedure_error);
    void reset_procedure(Client::Error procedure_error);
    void advance_procedure(Client::Error procedure_error);
    void on_action_Start_Procedure_triggered();
    void on_action_Delete_Procedure_triggered();
    void on_action_Advance_Procedure_triggered();
    void on_action_Reset_Procedure_triggered();
    void on_actionViewStatus_triggered();
    void on_action_Participate_triggered();
    void on_action_Refresh_triggered();
    void on_actionViewVoters_triggered();
    void on_procedureTreeWidget_itemActivated(QTreeWidgetItem* item, int column);
    void on_action_Open_Console_triggered();
    void on_action_Options_triggered();
    void on_action_Create_Users_triggered();
    void procedure_selected();
    void client_error(QAbstractSocket::SocketError socket_error);

protected:
    void contextMenuEvent(QContextMenuEvent *event);

private:
    Ui::ServerWindow ui;
    std::vector<Procedure> procedure_vec;

    Client* client;
    ConsoleDialog* console;
};

#endif // SERVERWINDOW_H
