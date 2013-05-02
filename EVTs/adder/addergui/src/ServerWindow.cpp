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
#include <vector>

#include "ServerWindow.h"
#include "ConnectDialog.h"
#include "Client.h"
#include "Procedure.h"
#include "ProcWizard.h"
#include "StatusDialog.h"
#include "LoginDialog.h"
#include "CreateKeypairDialog.h"
#include "CreateSecretShareDialog.h"
#include "SavePrivateKeyDialog.h"
#include "SelectChoiceDialog.h"
#include "SubmitPartialDecryptionDialog.h"
#include "VotersWidget.h"
#include "ConsoleDialog.h"
#include "SettingsDialog.h"
#include "CreateUsersDialog.h"

using namespace std;

ServerWindow::ServerWindow(QWidget *parent)
    : QMainWindow(parent)
{
	qDebug() << "Initializing TLS plugin...";
	
	QCoreApplication::addLibraryPath("plugins");
    if (!QCA::isSupported("tls")) {
        qDebug() << "failed";
        exit(EXIT_FAILURE);
    } else {
        qDebug() << "done\n";
    }
    ui.setupUi(this);

    client = new Client(0);
	
    refresh_procedure_list(std::vector<Procedure>());

    connect(ui.action_Connect, SIGNAL(triggered()), this, SLOT(open_connect_dialog()));
    connect(ui.actionAbout_Qt, SIGNAL(triggered()), qApp, SLOT(aboutQt()));
    connect(ui.action_About, SIGNAL(triggered()), this, SLOT(open_about_dialog()));
    
    connect(ui.action_Create_Procedure, SIGNAL(triggered()), this, SLOT(open_create_proc_wizard()));

    connect(ui.procedureTreeWidget, SIGNAL(itemSelectionChanged()),
            this, SLOT(procedure_selected()));

    connect(client, SIGNAL(disconnected()), this, SLOT(client_disconnect()));
    //    connect(client, SIGNAL(connected()), this, SLOT(client_connect()));
    connect(ui.action_Disconnect, SIGNAL(triggered()), client, SLOT(disconnect()));
    connect(client, SIGNAL(got_procedure_list(std::vector<Procedure>)),
            this, SLOT(refresh_procedure_list(std::vector<Procedure>)));
    connect(client, SIGNAL(create_procedure(Client::Error)),
            this, SLOT(create_procedure(Client::Error)));
    connect(client, SIGNAL(delete_procedure(Client::Error)),
            this, SLOT(delete_procedure(Client::Error)));
    connect(client, SIGNAL(start_procedure(Client::Error)),
            this, SLOT(start_procedure(Client::Error)));
    connect(client, SIGNAL(advance_procedure(Client::Error)),
            this, SLOT(advance_procedure(Client::Error)));
    connect(client, SIGNAL(reset_procedure(Client::Error)),
            this, SLOT(reset_procedure(Client::Error)));
    connect(client, SIGNAL(error(QAbstractSocket::SocketError)), 
            this, SLOT(client_error(QAbstractSocket::SocketError)));
    
    setFocusProxy(ui.procedureTreeWidget);

    QStringList headers;
    headers << tr("Title") << tr("Stage"); // << tr("Authorites needed");
    ui.procedureTreeWidget->setHeaderLabels(headers);

    QFontMetrics fm = fontMetrics();
    QHeaderView* header = ui.procedureTreeWidget->header();
    header->resizeSection(0, fm.width(tr("This is a typical procedure and then a whole lot more")));
    header->resizeSection(1, fm.width(tr("Authority polynomial data submission")));
    //    header->resizeSection(2, fm.width("Authorities Left       "));

    //    resize(sizeHint());
    console = new ConsoleDialog(client, this);
}

QSize ServerWindow::sizeHint() const
{
    const QHeaderView *header = ui.procedureTreeWidget->header();
    
    int width = 0;
    for (int i = 0; i < header->count(); ++i)
        width += header->sectionSize(i);
    
    return QSize(width, QMainWindow::sizeHint().height())
        .expandedTo(QApplication::globalStrut());
}

void ServerWindow::contextMenuEvent(QContextMenuEvent* event)
{
    ui.menu_Procedure->exec(event->globalPos());
}

void ServerWindow::open_connect_dialog()
{
    ConnectDialog* connect_dialog = new ConnectDialog(client, this);
    
    if (connect_dialog->exec()) {
        client_connect();
    }
}

void ServerWindow::procedure_selected()
{
    ui.action_Create_Procedure->setEnabled(client->get_is_admin());
    ui.action_Create_Users->setEnabled(client->get_is_admin());

    QList<QTreeWidgetItem*> item_list = ui.procedureTreeWidget->selectedItems();

    if (item_list.size() == 0) {
        ui.action_Delete_Procedure->setEnabled(false);
        ui.action_Advance_Procedure->setEnabled(false);
        ui.action_Reset_Procedure->setEnabled(false);
        ui.action_Start_Procedure->setEnabled(false);
        ui.actionViewStatus->setEnabled(false);
        ui.action_Participate ->setEnabled(false);
        ui.actionViewVoters->setEnabled(false);
    } else {
        QTreeWidgetItem* item = item_list.at(0);
        
        int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);
        Procedure proc = procedure_vec[row];
        
        ui.action_Delete_Procedure->setEnabled(true && client->get_is_admin());
        ui.action_Start_Procedure
            ->setEnabled((proc.get_remaining() == 0 ||
                         proc.get_stage() == Procedure::STAGE_NOTSTARTED)
                         && client->get_is_admin());
        ui.action_Reset_Procedure
            ->setEnabled(proc.get_stage() != Procedure::STAGE_NOTSTARTED &&
                         client->get_is_admin());
        ui.actionViewStatus->setEnabled(true);
        ui.action_Participate
            ->setEnabled(proc.get_stage() != Procedure::STAGE_NOTSTARTED &&
                         proc.get_stage() != Procedure::STAGE_FINISHED);
        ui.actionViewVoters->setEnabled(proc.get_stage() >= Procedure::STAGE_VOTING);
    }
}

void ServerWindow::open_create_proc_wizard()
{
    ProcWizard wizard(client);
    wizard.exec();
}

void ServerWindow::open_about_dialog()
{
    QDialog* dialog = new QDialog;
    Ui::AboutDialog ui;
    ui.setupUi(dialog);
    dialog->show();
}

void ServerWindow::client_disconnect()
{
    ui.action_Connect->setEnabled(true);
    ui.action_Disconnect->setEnabled(false);
    ui.action_Refresh->setEnabled(false);
    ui.action_Create_Procedure->setEnabled(false);
    ui.action_Create_Users->setEnabled(false);

    ui.procedureTreeWidget->clear();
    procedure_selected();
}

void ServerWindow::client_connect()
{
    ui.action_Connect->setEnabled(false);
    ui.action_Disconnect->setEnabled(true);
    ui.action_Refresh->setEnabled(true);

    client->request_procedure_list();
}

void ServerWindow::refresh_procedure_list(std::vector<Procedure> procedure_vec)
{
    QList<QTreeWidgetItem*> item_list = ui.procedureTreeWidget->selectedItems();

    string cur_id;
    if (item_list.size() == 1) {
        QTreeWidgetItem* item = item_list.at(0);
        int index = ui.procedureTreeWidget->indexOfTopLevelItem(item);
        cur_id = this->procedure_vec[index].get_id();
    }

    this->procedure_vec = procedure_vec;
    ui.procedureTreeWidget->clear();

    QTreeWidgetItem* item_to_be_selected = 0;
    vector<Procedure>::iterator i;
    for (i = procedure_vec.begin(); i < procedure_vec.end(); i++) {
        QTreeWidgetItem* item = new QTreeWidgetItem(ui.procedureTreeWidget);

        item->setText(0, QString(i->get_title().c_str()));
        item->setText(1, QString(i->get_stage_desc().c_str()));

        /* If the procedure is finished, then we want to display 0
           authorities remaining.  Otherwise, we display the number that
           are actually remaining. 
        */
        if (i->get_stage() == Procedure::STAGE_FINISHED) {
            item->setText(2, "0");
        } else {
            item->setText(2, QString::number(i->get_remaining()));
        }

        item->setTextAlignment(2, Qt::AlignRight);

        if (i->get_id() == cur_id) {
            item_to_be_selected = item;
        }
    }

    if (item_to_be_selected) {
        ui.procedureTreeWidget->setItemSelected(item_to_be_selected, true);
        ui.procedureTreeWidget->setCurrentItem(item_to_be_selected);
    }

    procedure_selected();
}

void ServerWindow::create_procedure(Client::Error procedure_error)
{
    switch(procedure_error) {
    case Client::OK:
        client->request_procedure_list();
        break;
    case Client::Failure:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Procedure could not be created.\n"
                                 "You have entered some invalid parameters."));
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error creating procedure."));
    }
}

void ServerWindow::delete_procedure(Client::Error procedure_error)
{
    switch(procedure_error) {
    case Client::OK:
        client->request_procedure_list();
        break;
    case Client::Failure:
        QMessageBox::warning(this, tr("AdderGUI"),
                             tr("Error deleting procedure:\n"
                                "This procedure does not exist."));
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error deleting procedure."));
    }
}

void ServerWindow::start_procedure(Client::Error procedure_error)
{
    switch(procedure_error) {
    case Client::OK:
        client->request_procedure_list();
        break;
    case Client::Badprocedure:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Error starting procedure:\n"
                                 "This procedure does not exist."));
        break;
    case Client::Badstage:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Error starting procedure:\n"
                                 "This procedure is already started."));
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error starting procedure.\n"));
    }
}

void ServerWindow::advance_procedure(Client::Error procedure_error)
{
    switch(procedure_error) {
    case Client::OK:
        client->request_procedure_list();
        break;
    case Client::Badprocedure:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Error advancing procedure:\n"
                                 "This procedure does not exist."));
        break;
    case Client::Badstage:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Error advancing procedure:\n"
                                 "This procedure cannot be advanced further."));
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error advancing procedure.\n"));
    }
}

void ServerWindow::reset_procedure(Client::Error procedure_error)
{
    switch(procedure_error) {
    case Client::OK:
        client->request_procedure_list();
        break;
    case Client::Badprocedure:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("Error resetting procedure:\n"
                                 "This procedure does not exist."));
        break;
    default:
        QMessageBox::critical(this, tr("AdderGUI"),
                              tr("Unknown error resetting procedure.\n"));
    }
}

void ServerWindow::on_action_Start_Procedure_triggered()
{
    QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
    int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);
    
    if (procedure_vec[row].get_stage() == Procedure::STAGE_NOTSTARTED) {
        client->start_procedure(QString(procedure_vec[row].get_id().c_str()));
    } else {
        on_action_Advance_Procedure_triggered();
    }
}

void ServerWindow::on_action_Delete_Procedure_triggered()
{
    if (QMessageBox::question(this,
                                 tr("AdderGUI"),
                                 tr("Deleting a procedure will make it impossible\n"
                                    "to recover any information about this procedure,\n"
                                    "including its results."),
                                 tr("&Delete"), tr("Cancel"),
                                 QString(), 0, 1) == 0) {
        
        QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
        int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);
        client->delete_procedure(QString(procedure_vec[row].get_id().c_str()));
    }
}

void ServerWindow::on_action_Advance_Procedure_triggered()
{
    if (QMessageBox::question(this,
                             tr("AdderGUI"),
                             tr("Advance procedure?"),
                             tr("&Advance"), tr("Cancel"),
                             QString(), 0, 1) == 0) {
        
        QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
        int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);
        client->advance_procedure(QString(procedure_vec[row].get_id().c_str()));
    }
}

void ServerWindow::on_action_Reset_Procedure_triggered()
{
    if (QMessageBox::question(this,
                              tr("AdderGUI"),
                              tr("Resetting a procedure will make it impossible\n"
                                 "to recover any information about this procedure,\n"
                                 "including its results."),
                              tr("&Reset"), tr("Cancel"),
                              QString(), 0, 1) == 0) {
        QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
        int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);
        client->reset_procedure(QString(procedure_vec[row].get_id().c_str()));
    }
}

void ServerWindow::on_actionViewStatus_triggered()
{
    QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
    int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);

    if (row >= 0 && row < procedure_vec.size()) {
        StatusDialog* dialog = new StatusDialog(procedure_vec[row],
                                                client, this);
        dialog->show();
    }
}

void ServerWindow::on_procedureTreeWidget_itemActivated(QTreeWidgetItem*,
                                                        int)
{
    on_actionViewStatus_triggered();
}

void ServerWindow::on_action_Participate_triggered()
{
    QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
    int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);
    QString proc_id = QString(procedure_vec[row].get_id().c_str());
    int stage = procedure_vec[row].get_stage();
    
    if (stage == Procedure::STAGE_NOTSTARTED) {
        QMessageBox::information(this, tr("AdderGUI"),
                                 tr("The procedure is not yet started."));
        return;
    }
    
    QString user_id;
    QString password;
    LoginDialog* login = new LoginDialog(client, proc_id, &user_id, &password,
                                         this);
    
    if (login->exec()) {
        CreateKeypairDialog* keypairdialog;
        CreateSecretShareDialog* secretsharedialog;
        SavePrivateKeyDialog* saveprivkeydialog;
        SelectChoiceDialog* selectchoicedialog;
        SubmitPartialDecryptionDialog* submitpartialdecryptiondialog;

        switch (stage) {
        case Procedure::STAGE_WAITKEYS:
            keypairdialog = new CreateKeypairDialog(client, proc_id, 
                                                    user_id, password, this);
            keypairdialog->exec();
            break;
        case Procedure::STAGE_WAITPOLYNOMIAL:
            secretsharedialog = new CreateSecretShareDialog(client,
                                                            procedure_vec[row],
                                                            user_id,
                                                            this);
            secretsharedialog->exec();
            break;
        case Procedure::STAGE_WAITGETPRIVKEYS:
            saveprivkeydialog = new SavePrivateKeyDialog(client,
                                                         procedure_vec[row],
                                                         user_id,
                                                         password,
                                                         this);
            saveprivkeydialog->exec();
            break;
        case Procedure::STAGE_VOTING:
            selectchoicedialog = new SelectChoiceDialog(client,
                                                        procedure_vec[row],
                                                        user_id,
                                                        this);
            selectchoicedialog->exec();
            break;
        case Procedure::STAGE_WAITDECRYPT:
            submitpartialdecryptiondialog = 
                new SubmitPartialDecryptionDialog(client,
                                                  procedure_vec[row],
                                                  user_id,
                                                  password,
                                                  this);
            submitpartialdecryptiondialog->exec();
            break;
        default:
            QMessageBox::information(this, tr("AdderGUI"),
                                     tr("Participation is not possible at this stage."));
            break;
        }
    }

    client->request_procedure_list();
}

void ServerWindow::on_action_Refresh_triggered()
{
    client->request_procedure_list();
}

void ServerWindow::on_actionViewVoters_triggered()
{
    QTreeWidgetItem* item = ui.procedureTreeWidget->currentItem();
    int row = ui.procedureTreeWidget->indexOfTopLevelItem(item);

    VotersWidget* voters_dialog = 
        new VotersWidget(procedure_vec[row], client, this);
    voters_dialog->show();
}

void ServerWindow::on_action_Open_Console_triggered()
{
    console->show();
}

void ServerWindow::client_error(QAbstractSocket::SocketError socket_error)
{
    switch (socket_error) {
    case QAbstractSocket::RemoteHostClosedError:
        QMessageBox::warning(this, tr("AdderGUI"),
                             tr("The remote host has closed the connection.\n"));
        break;
    default:
        break;
    }
}

void ServerWindow::on_action_Options_triggered()
{
    SettingsDialog* settings_dialog = new SettingsDialog(this);
    settings_dialog->show();
}

void ServerWindow::on_action_Create_Users_triggered()
{
    CreateUsersDialog* create_dialog = new CreateUsersDialog(client, this);
    create_dialog->show();
}
