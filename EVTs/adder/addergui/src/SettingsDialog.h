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

#ifndef SETTINGSDIALOG_H
#define SETTINGSDIALOG_H

#include "ui_settingsdialog.h"

class SettingsDialog : public QDialog
{
    Q_OBJECT
    
public:
    SettingsDialog(QWidget* parent = 0);
    
public slots:
    void on_applyPushButton_clicked();
    void on_okPushButton_clicked();
    void changePage(QListWidgetItem* current, QListWidgetItem* previous);
    
private:
    Ui::SettingsDialog ui;
};

#endif // SETTINGSDIALOG_H

