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

#include "settings_pages.h"

SettingsKeysWidget::SettingsKeysWidget(QWidget* parent)
    : QWidget(parent)
{
    ui.setupUi(this);

    QSettings settings;
    settings.beginGroup("keys");
    ui.dirLineEdit->setText(settings.value("key_dir").toString());
    ui.pubkeyLineEdit->setText(settings.value("pubkey_file").toString());
    ui.privkeyLineEdit->setText(settings.value("privkey_file").toString());
    ui.polyLineEdit->setText(settings.value("polynomial_file").toString());
    ui.privkey2LineEdit->setText(settings.value("privkey2_file").toString());
    settings.endGroup();
}

void SettingsKeysWidget::on_dirPushButton_clicked()
{
    QString s = QFileDialog::getExistingDirectory();
	if (!s.isEmpty()) {
		ui.dirLineEdit->setText(s);
	}
}

void SettingsKeysWidget::apply()
{
    QSettings settings;
    settings.beginGroup("keys");
    settings.setValue("key_dir", ui.dirLineEdit->text());
    settings.setValue("pubkey_file", ui.pubkeyLineEdit->text());
    settings.setValue("privkey_file", ui.privkeyLineEdit->text());
    settings.setValue("polynomial_file", ui.polyLineEdit->text());
    settings.setValue("privkey2_file", ui.privkey2LineEdit->text());
    settings.endGroup();
}

SettingsSSLWidget::SettingsSSLWidget(QWidget* parent)
    : QWidget(parent)
{
    ui.setupUi(this);

    QSettings settings;
    settings.beginGroup("ssl");
    ui.certTextEdit->setText(settings.value("certificate").toString());
    settings.endGroup();
}

void SettingsSSLWidget::apply()
{
    QSettings settings;
    settings.beginGroup("ssl");
    settings.setValue("certificate", ui.certTextEdit->toPlainText());
    settings.endGroup();
}
