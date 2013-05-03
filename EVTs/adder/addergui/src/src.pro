BASE = ..

TEMPLATE = app
QT += network
RESOURCES = ..\resource.qrc
TARGET = addergui

CONFIG += qt release

include($$BASE/conf.pri)

unix:{
	CONFIG += link_pkgconfig
	PKGCONFIG += libadder qca
	LIBS += -lboost_regex

	target.path = $$BINDIR
	INSTALLS += target
}

windows:{
	#CONFIG += console
	LIBS += "C:\Documents and Settings\mkorman\Desktop\gmp-4.1.4\Release\gmp.lib" \
			"C:\Documents and Settings\mkorman\My Documents\Visual Studio Projects\adder\libadder\src\Release\libadder.lib" \
			"C:\qca-2.0-beta2\lib\qca2.lib" \
			"C:\qca-openssl-0.1-20060406\release\qca-openssl.lib" \
			"shell32.lib" \
			"advapi32.lib"
			
	INCLUDEPATH += "C:\Documents and Settings\mkorman\Desktop\gmp-4.1.4" \
			       "C:\Documents and Settings\mkorman\My Documents\Visual Studio Projects\adder\libadder\src" \
				   "C:\Documents and Settings\mkorman\Desktop\boost_1_33_1" \
	                C:\qca-2.0-beta2\include\QtCrypto
}

# Input
HEADERS += ConnectDialog.h \
	ServerWindow.h \
	Client.h \
	Procedure.h \
	ProcWizard.h \
	SimpleWizard.h \
	StatusDialog.h \
	LoginDialog.h \
	CreateKeypairDialog.h \
        key_management.h \
        CreateSecretShareDialog.h \
        SavePrivateKeyDialog.h \
        SelectChoiceDialog.h \
        SubmitPartialDecryptionDialog.h \
        VotersWidget.h \
        ViewVoterDialog.h \
        ConsoleDialog.h \
        SettingsDialog.h \
        settings_pages.h \
        CreateUsersDialog.h
FORMS += connectdialog.ui \
	serverwindow.ui \
	aboutdialog.ui \
	procwizardchoicespage.ui \
	procwizardthresholdpage.ui \
	procwizardtitlepage.ui \
	procwizarddeadlinespage.ui \
	statusdialog.ui \
	logindialog.ui \
	createkeypairdialog.ui \
        createsecretsharedialog.ui \
        saveprivatekeydialog.ui \
        selectchoicedialog.ui \
        submitpartialdecryptiondialog.ui \
        voterswidget.ui \
        viewvoterdialog.ui \
        consoledialog.ui \
        settingsdialog.ui \
        settingskeyswidget.ui \
        settingssslwidget.ui \
        createusersdialog.ui
SOURCES += main.cpp \
	ConnectDialog.cpp \
	ServerWindow.cpp \
	Client.cpp \
	Procedure.cpp \
	ProcWizard.cpp \
	SimpleWizard.cpp \
	StatusDialog.cpp \
	LoginDialog.cpp \
	CreateKeypairDialog.cpp \
        key_management.cpp \
        CreateSecretShareDialog.cpp \
        SavePrivateKeyDialog.cpp \
        SelectChoiceDialog.cpp \
        SubmitPartialDecryptionDialog.cpp \
        VotersWidget.cpp \
        ViewVoterDialog.cpp \
        ConsoleDialog.cpp \
        SettingsDialog.cpp \
        settings_pages.cpp \
        CreateUsersDialog.cpp
