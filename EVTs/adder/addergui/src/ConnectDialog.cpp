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

#include "ConnectDialog.h"
#include "Client.h"

using namespace std;

ConnectDialog::ConnectDialog(Client* client, QWidget *parent)
    : QDialog(parent), client(client)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    connect(ui.cancelButton, SIGNAL(clicked()), this, SLOT(reject()));

    connect(client, SIGNAL(connected()), this, SLOT(client_connect()));
    connect(client, SIGNAL(error(QAbstractSocket::SocketError)), 
            this, SLOT(display_error(QAbstractSocket::SocketError)));
    connect(client, SIGNAL(admin(Client::Error)),
            this, SLOT(admin(Client::Error)));

    progress = new QProgressDialog("Looking up host...", "Cancel", 0, 0, this);

    QSettings settings;
    settings.beginGroup("server");
    ui.hostnameLineEdit->setText(settings.value("hostname").toString());
    ui.portSpinBox->setValue(settings.value("port", 6999).toInt());
    ui.sslCheckBox->setCheckState
        (Qt::CheckState(settings.value("use_ssl", true).toBool() 
                        ? Qt::Checked
                        : Qt::Unchecked));
    settings.endGroup();
}

void ConnectDialog::client_connect()
{
    if (ui.adminCheckBox->checkState() == Qt::Checked) {
        client->admin(ui.adminLineEdit->text());
    } else {
        accept();
    }

    QSettings settings;
    settings.beginGroup("server");
    settings.setValue("hostname", ui.hostnameLineEdit->text());
    settings.setValue("port", ui.portSpinBox->value());
    settings.setValue("use_ssl", 
                      ui.sslCheckBox->checkState() == Qt::Checked 
                      ? true 
                      : false);
    settings.endGroup();
}

void ConnectDialog::admin(Client::Error error)
{
    switch (error) {
    case Client::OK:
        accept();
        break;
    default:
        QMessageBox::warning(this,
                             tr("AdderGUI"),
                             tr("Administrator password incorrect."));
        break;
    }
}

void ConnectDialog::on_connectButton_clicked()
{
    if (ui.sslCheckBox->checkState() == Qt::Checked) {
        client->set_using_ssl(true);
    }
        
    client->connect_to_host(ui.hostnameLineEdit->text(), ui.portSpinBox->value());

    connect(client, SIGNAL(connected()),
            progress, SLOT(cancel()));

    connect(client, SIGNAL(disconnected()),
            progress, SLOT(cancel()));

    connect(client, SIGNAL(hostFound()), this, SLOT(host_found()));
    connect(progress, SIGNAL(canceled()), client, SLOT(disconnect()));

    progress->setValue(1);
}

void ConnectDialog::on_adminCheckBox_stateChanged(int state)
{
    ui.adminLabel->setEnabled(state == Qt::Checked);
    ui.adminLineEdit->setEnabled(state == Qt::Checked);
}

void ConnectDialog::host_found()
{
    progress->setLabelText("Connecting to host...");
}

void ConnectDialog::display_error(QAbstractSocket::SocketError socket_error)
{
    progress->cancel();

    switch (socket_error) {
    case QAbstractSocket::HostNotFoundError:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("The host was not found.\n"
                                 "Please check the "
                                 "host name and port settings."));
        break;
    case QAbstractSocket::ConnectionRefusedError:
        QMessageBox::warning(this, tr("AdderGUI"),
                              tr("The connection was refused by the peer.\n"
                                 "Make sure the Adder server is running, \n"
                                 "and check that the host name and port \n"
                                 "settings are correct."));
        break;
    case QAbstractSocket::RemoteHostClosedError:
        QMessageBox::warning(this, tr("AdderGUI"),
                             tr("The remote host has closed the connection.\n"));
        break;
    default:
        break;
    }
}
