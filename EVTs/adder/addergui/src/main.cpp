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

#include <QtCore>
#include <QtGui>
#include <QtNetwork>
#include <QtCrypto>

#include "key_management.h"

#include "ServerWindow.h"

#include <iostream>

using namespace std;

void set_key_settings()
{
    QSettings settings;
    settings.beginGroup("keys");
    if (!settings.contains("key_dir")) {
        settings.setValue("key_dir", default_adder_directory());
    }
    
    if (!settings.contains("pubkey_file")) {
        settings.setValue("pubkey_file", QString("pubkey.adder"));
    }

    if (!settings.contains("privkey_file")) {
        settings.setValue("privkey_file", QString("privkey.adder"));
    }

    if (!settings.contains("polynomial_file")) {
        settings.setValue("polynomial_file", QString("polynomial.adder"));
    }

    if (!settings.contains("privkey2_file")) {
        settings.setValue("privkey2_file", QString("privkey2.adder"));
    }

    settings.endGroup();
}

int main(int argc, char* argv[])
{
	cout << QDir::homePath().toStdString() << endl;
    QCA::Initializer init;

    QApplication app(argc, argv);

    QCoreApplication::setOrganizationName("Adder");
    QCoreApplication::setOrganizationDomain("cryptodrm.engr.uconn.edu");
    QCoreApplication::setApplicationName("AdderGUI");

    set_key_settings();
    
    ServerWindow* ui = new ServerWindow;
    ui->show();

    return app.exec();
}
