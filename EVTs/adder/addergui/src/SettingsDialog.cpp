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

#include "SettingsDialog.h"
#include "settings_pages.h"

using namespace std;

SettingsDialog::SettingsDialog(QWidget *parent)
    : QDialog(parent)
{
    setAttribute(Qt::WA_DeleteOnClose);
    ui.setupUi(this);

    ui.contentsWidget->setMaximumWidth(120);

    ui.pagesStackedWidget->addWidget(new SettingsKeysWidget);
    ui.pagesStackedWidget->addWidget(new SettingsSSLWidget);

    QListWidgetItem *keyButton = new QListWidgetItem(ui.contentsWidget);
    keyButton->setIcon(QIcon(":/images/folder_big.png"));
    keyButton->setText(tr("Key Locations"));
    keyButton->setTextAlignment(Qt::AlignHCenter);
    keyButton->setFlags(Qt::ItemIsSelectable | Qt::ItemIsEnabled);

    QListWidgetItem *sslButton = new QListWidgetItem(ui.contentsWidget);
    sslButton->setIcon(QIcon(":/images/key.png"));
    sslButton->setText(tr("SSL"));
    sslButton->setTextAlignment(Qt::AlignHCenter);
    sslButton->setFlags(Qt::ItemIsSelectable | Qt::ItemIsEnabled);

    ui.contentsWidget->setCurrentRow(0);

    connect(ui.contentsWidget,
            SIGNAL(currentItemChanged(QListWidgetItem *, QListWidgetItem *)),
            this, SLOT(changePage(QListWidgetItem *, QListWidgetItem*)));
}

void SettingsDialog::on_applyPushButton_clicked()
{
    ((SettingsKeysWidget*)(ui.pagesStackedWidget->widget(0)))->apply();
    ((SettingsSSLWidget*)(ui.pagesStackedWidget->widget(1)))->apply();
}

void SettingsDialog::on_okPushButton_clicked()
{
    on_applyPushButton_clicked();
    accept();
}

void SettingsDialog::changePage(QListWidgetItem *current, QListWidgetItem *previous)
{
    if (!current)
        current = previous;
    
    ui.pagesStackedWidget->setCurrentIndex(ui.contentsWidget->row(current));
}
