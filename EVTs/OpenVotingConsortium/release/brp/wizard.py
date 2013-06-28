#!/usr/bin/env python

# TODOs: Fix progressbar updating (04/19)

import sys, os, commands, time
from datetime import date  # Only available in Python 2.3+
from qt import *
from qttable import *
from gnosis.xml.objectify import make_instance
import evm2003.utils.equiv  # Must import module whole
from evm2003.utils.getxml import ballotxml
from evm2003.utils.convert import digits2votes, votes2digits, obscure

# Looks like we need a debug mode

def inDebugMode():
    if "-debug" in sys.argv:
        return True
    else:
        return False

# Special UI Components
# -----------------------------------------------------------------------------

class WarningHandler(QObject):
    def showWarning(self, warning):
        self.warningLabel.setText("<b>Error</b>: " + warning)
        self.warningLabel.show()
#         try:
#             self.errorLog.write(warning)
#         except AttributeError:
#             self.parent().errorLog.write(warning)

    def clearWarning(self):
        self.warningLabel.hide()


class LoginBox(QWidget, WarningHandler):
    def __init__(self, parent, name, userLabel, authHandler):
        QWidget.__init__(self, parent, name)

        self.isLoggedIn = False
        self.userLabel = userLabel
        self.authHandler = authHandler
        self.userNameList = self.authHandler.getAccessControlListNames()
        self.userNameList.sort()

        gridLayout = QGridLayout(self, 4, 2, 0, 6)
        self.warningLabel = WarningLabel("", self)
        gridLayout.addMultiCellWidget(self.warningLabel, 0, 0, 0, 1)
        self.nameLabel = QLabel(userLabel, self)
#         self.nameLabel.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Preferred)
        gridLayout.addWidget(self.nameLabel, 1, 0)
        self.nameWidgetStack = QWidgetStack(self)
        self.nameWidgetStack.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Preferred)
        self.nameComboBox = QComboBox(self)
        self.nameComboBox.insertStrList(self.userNameList)
        self.nameWidgetStack.addWidget(self.nameComboBox, 0)
        self.currentNameLabel = QLabel("", self)
        self.nameWidgetStack.addWidget(self.currentNameLabel, 1)
        gridLayout.addWidget(self.nameWidgetStack, 1, 1)
        self.passwordLabel = QLabel("Password", self)
        gridLayout.addWidget(self.passwordLabel, 2, 0)
        self.passwordLineEdit = QLineEdit(self)
        self.passwordLineEdit.setEchoMode(QLineEdit.Password)
        gridLayout.addWidget(self.passwordLineEdit, 2, 1)
        self.loginButton = QPushButton("Log In As %s" % userLabel, self)
        self.connect(self.loginButton, SIGNAL("clicked()"), self.checkLoginAttempt)
        gridLayout.addMultiCellWidget(self.loginButton, 3, 3, 0, 1)

    def checkLoginAttempt(self):
        userLabel = self.loginButton.text()
        userName = str(self.nameComboBox.currentText())
        password = self.passwordLineEdit.text()

        if self.isLoggedIn:
            self.setLoggedOutState()
        else:
            if self.authHandler.checkPassword(userName, password):
                self.setLoggedInState(userName)
            else:
                self.showWarning("Authentication failed, try again.")

    def updateNameComboBox(self, userNameList):
        self.userNameList = userNameList
        self.userNameList.sort()
        self.nameComboBox.clear()
        self.nameComboBox.insertStrList(userNameList)

    def setLoggedInState(self, userName):
        self.isLoggedIn = True
        self.warningLabel.hide()
        self.passwordLabel.hide()
        self.passwordLineEdit.hide()
        self.currentNameLabel.setText(userName)
        self.nameWidgetStack.raiseWidget(1)
        self.loginButton.setText("Log %s Out" % self.userLabel)
        self.authHandler.setRole(self.userLabel, userName)
        self.userNameList.remove(userName)
        self.emit(PYSIGNAL("updateNames"), (self.userNameList,))

    def setLoggedOutState(self):
        self.isLoggedIn = False
        self.passwordLabel.show()
        self.passwordLineEdit.clear()
        self.passwordLineEdit.show()
        self.userNameList.append(str(self.currentNameLabel.text()))
        self.updateNameComboBox(self.userNameList)
        self.emit(PYSIGNAL("updateNames"), (self.userNameList,))
        self.nameWidgetStack.raiseWidget(0)
        self.currentNameLabel.setText("")
        self.loginButton.setText("Log In As %s" % self.userLabel)
        self.authHandler.delRole(self.userLabel)
        self.parent().parent().disableNext()  # Encapsulation power!


class LogoutBox(QWidget, WarningHandler):
    def __init__(self, parent, roleName, authHandler):
        QWidget.__init__(self, parent)

        self.authHandler = authHandler
        self.roleName = roleName
        self.userName = '<user name>' # won't know true value on init, handled below

        gridLayout = QGridLayout(self, 4, 2, 0, 6)
        self.warningLabel = WarningLabel("", self)
        gridLayout.addMultiCellWidget(self.warningLabel, 0, 0, 0, 1)
        self.currentUserLabel = QLabel("%s: %s" % (self.roleName, self.userName), self)
        gridLayout.addMultiCellWidget(self.currentUserLabel, 1, 1, 0, 1)
        self.passwordLabel = QLabel("Password", self)
        gridLayout.addWidget(self.passwordLabel, 2, 0)
        self.passwordLineEdit = QLineEdit(self)
        self.passwordLineEdit.setEchoMode(QLineEdit.Password)
        gridLayout.addWidget(self.passwordLineEdit, 2, 1)
        self.logoutButton = QPushButton("Log Out As %s" % self.roleName, self)
        self.connect(self.logoutButton, SIGNAL("clicked()"), self.checkLogoutAttempt)
        gridLayout.addMultiCellWidget(self.logoutButton, 3, 3, 0, 1)

    def checkLogoutAttempt(self):
        password = self.passwordLineEdit.text()
        if self.authHandler.checkPassword(self.userName, password):
            self.setLoggedOutState()
        else:
            self.showWarning("Authentication failed, try again.")

    def setLoggedOutState(self):
        self.isLoggedIn = False
        self.passwordLineEdit.setEnabled(False)
        self.logoutButton.setEnabled(False)
        self.authHandler.delRole(self.roleName)

    def updateUserName(self):
        self.userName = self.authHandler.getName(self.roleName)
        self.currentUserLabel.setText("%s: %s" % (self.roleName, self.userName))


class InputLine(QLineEdit):
    def __init__(self, *args):
        QLineEdit.__init__(self, *args)
        self.setFocus()  # This doesn't seem to register...

    def focusInEvent(self, event):
        if event.gotFocus():
            self.setPaletteBackgroundColor(QColor(153, 204, 153))
            self.setFocus()
            QLineEdit.focusInEvent(self, event)

    def focusOutEvent(self, event):
        if event.lostFocus():
            self.setPaletteBackgroundColor(QColor(255, 153, 153))
            QLineEdit.focusOutEvent(self, event)


class InfoLabel(QLabel):
    def __init__(self, *args):
        QLabel.__init__(self, *args)
        self.setPaletteBackgroundColor(QColor(255, 255, 238))
        self.setFrameShape(QLabel.Box)
        self.setMargin(2)


class WarningLabel(InfoLabel):
    def __init__(self, *args):
        InfoLabel.__init__(self, *args)
        self.setPaletteBackgroundColor(QColor(255, 235, 232))
        self.hide()  # Always start out hidden


class Table(QTable):
    def __init__(self, *args):
        QTable.__init__(self, *args)
        self.setReadOnly(True)
        self.setSelectionMode(QTable.NoSelection)


# I/O components
# -----------------------------------------------------------------------------

class AuthenticationHandler(QObject):
    def __init__(self, parent, fileName):
        QObject.__init__(self, parent)
        self.loadAccessControlList(fileName)
        self.roles = {}

    def loadAccessControlList(self, fileName):
        accessControlList = QFile(fileName)
        accessControlList.open(IO_ReadOnly)
        self.__acl = dict([acct.strip().split(';') for acct in str(accessControlList.readAll()).strip().split('\n')])

    def getAccessControlListNames(self):
        return self.__acl.keys()

    def checkPassword(self, name, password):
        return self.__acl[name] == password

    def setRole(self, role, userName):
        self.roles[role] = userName  # We can do much better for error handling here
        self.checkRoleRegistry()
        self.parent().eventLog.write("%s logged in as role %s" % (userName, role))

    def getName(self, role):
        return self.roles[role]

    def getRole(self, name):
        for role in roles:
            if roles[role] == name:
                return role

    def delRole(self, role):
        userName = self.roles[role]
        del self.roles[role]
        self.checkRoleRegistry()
        self.parent().eventLog.write("%s logged out of role %s" % (userName, role))

    def checkRoleRegistry(self):
        roleKeys = ('Operator', 'Witness One', 'Witness Two')
        if self.roles.has_key(roleKeys[0]) and self.roles.has_key(roleKeys[1]) and self.roles.has_key(roleKeys[2]):
            self.emit(PYSIGNAL("allUsersLoggedIn"), ())
        elif not self.roles:
            self.emit(PYSIGNAL("allUsersLoggedOut"), ())


class LogWriter(QObject):
    def __init__(self, logFileName):
        QObject.__init__(self)
        self.openLogFile(logFileName)

    def getTimeStamp(self):
        return QDateTime().currentDateTime().toString('[MM-dd-yyyy hh:mm:ss]')

    def openLogFile(self, logFileName):
        self.logFile = QFile(logFileName)
        self.logFile.open(IO_Raw | IO_WriteOnly)

    def closeLogFile(self):
        self.logFile.close()


class EventLogWriter(LogWriter):
    def __init__(self, logFile):
        LogWriter.__init__(self, logFile)

    def write(self, message):
        timeStamp = self.getTimeStamp()
        self.logFile.writeBlock("%s [Event] %s\n" % (timeStamp, message))
        self.logFile.flush()


class ErrorLogWriter(LogWriter):
    def __init__(self, logFile):
        LogWriter.__init__(self, logFile)

    def write(self, message):
        timeStamp = self.getTimeStamp()
        self.logFile.writeBlock("%s [Error] %s\n" % (timeStamp, message))
        self.logFile.flush()


class BallotReader(object):
    def __init__(self, electionMetaData):
        self.electionMetaData = electionMetaData

    def readBarcodeInput(self, barcode):
        ballotId = barcode[:4]
        votes = digits2votes(barcode)
        print votes
        writeIns = [['', ''], '', '', '', '', '', '', '', '', '', '', '', '']
        date = self.electionMetaData['date']
        country = self.electionMetaData['country']
        state = self.electionMetaData['state']
        county = self.electionMetaData['county']
        precinct = self.electionMetaData['precinct']
        serial = self.electionMetaData['serial']  # Must this be passed in here?
        fileType = self.electionMetaData['fileType']
        fileName = "b-%s-%s-%s-%s-%s-%s.xml" % (date.strftime('%Y%m%d'), country,
            state, county, precinct, ballotId)
        fileName = fileName.replace(' ', '_')
        # getxml.ballotxml() hacks up the date!
        ballotXML = ballotxml(date.strftime("%Y%m%d"), country, state, county, ballotId,
            precinct, serial, fileType, votes, writeIns)

        return (fileName, ballotXML)

    def readXMLInput(self, xml):
        pass


class BallotWriteError(Exception):
    pass


class BallotExistsError(BallotWriteError):
    def __init__(self, fileName):
        self.fileName = fileName


class BallotWriter(object):
    def __init__(self):
        self.fileHandler = QFile()

    def writeXMLFile(self, fileName, ballotXML):
        self.fileHandler.setName('scanned/' + fileName)
        if self.fileHandler.exists():
            raise BallotExistsError(fileName[-8:-4])
        else:
            self.fileHandler.open(IO_Raw | IO_WriteOnly)  # Best mode?
            self.fileHandler.writeBlock(str(ballotXML))  # Ensure a string is passed
            self.fileHandler.close()
        return fileName


class BarcodeValidator(QRegExpValidator):
    def __init__(self, *args):
        QRegExpValidator.__init__(self, *args)
        regexp = QRegExp("[0-9]{40}")
        self.setRegExp(regexp)

# Ballot Reconciliation UI
# -----------------------------------------------------------------------------

class BRPWizard(QWizard):
    def __init__(self, *args):
        QWizard.__init__(self, *args)

        self.setCaption("OVC Ballot Reconciliation System")
        self.authHandler = AuthenticationHandler(self, 'acl.txt')  # Checked on start-up
        self.__initData()

        self.eventLog = EventLogWriter('eventlog.txt')
        self.errorLog = ErrorLogWriter('errorlog.txt')

        font = QFont(self.font())
        font.setPointSize(12)
        font.setBold(True)
        self.setTitleFont(font)

        self.wizardPage1 = SignInPage(self, "Operator and Witness Sign-In", self.data, self.errorLog, self.authHandler)
        self.addPage(self.wizardPage1, self.wizardPage1.title)
        self.connect(self.wizardPage1, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage2 = ManualCountPage(self, "Paper Ballot Manual Count", self.data, self.errorLog)
        self.addPage(self.wizardPage2, self.wizardPage2.title)
        self.connect(self.wizardPage2, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage3 = ScanCountPage(self, "Paper Ballot Scan Count", self.data, self.errorLog)
        self.addPage(self.wizardPage3, self.wizardPage3.title)
        self.connect(self.wizardPage3, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage4 = LoadDataPage(self, "Load Vote Station Data", self.data, self.errorLog)
        self.addPage(self.wizardPage4, self.wizardPage4.title)
        self.connect(self.wizardPage4, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage5 = RegisterTestBallotsPage(self, "Register Test Ballots", self.data, self.errorLog)
        self.addPage(self.wizardPage5, self.wizardPage5.title)
        self.connect(self.wizardPage5, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage6 = RegisterSpoiledBallotsPage(self, "Register Spoiled Ballots", self.data, self.errorLog)
        self.addPage(self.wizardPage6, self.wizardPage6.title)
        self.connect(self.wizardPage6, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage7 = CompareBallotsPage(self, "Compare Ballots", self.data, self.errorLog)
        self.addPage(self.wizardPage7, self.wizardPage7.title)
        self.connect(self.wizardPage7, PYSIGNAL("enableNext"), self.setNextEnabled)

        self.wizardPage8 = SignOutPage(self, "Operator and Witness Sign-Out", self.data, self.errorLog, self.authHandler)
        self.addPage(self.wizardPage8, self.wizardPage8.title)
        self.connect(self.wizardPage8, PYSIGNAL("enableFinish"), self.setFinishEnabled)
        self.connect(self.wizardPage8, PYSIGNAL("disableBack"), self.setBackEnabled)

        if not inDebugMode():
            self.__disableNextPages()

        # Some pages we also don't want to be able to go back to
        self.setBackEnabled(self.wizardPage2, False)

        # We don't need the help button as instructions are integrated in each page
        self.__disableHelpButtons()

#         self.resize(QSize(400, 300).expandedTo(self.minimumSizeHint()))  # is this size alright?
        self.clearWState(Qt.WState_Polished)

    def __initData(self):
        self.data = {}  # very important; holds state data from each page & general metadata
        # we can load metadata from anywhere; see David M.'s code
        self.data['country'] = "US"
        self.data['state'] = "CA"
        self.data['county'] = "Santa Clara County"
        self.data['precinct'] = "2216"
        self.data['serial'] = "213"  # this should be pulled from each ballot; won't know what to
                                     # assign during barcode scan, but getxml.ballotxml() requires it
                                     # fix test ballots to produce matches
        self.data['date'] = date(2004, 11, 02)  # make sure all code has correct date
        self.data['fileType'] = 'scan'

    def __disableNextPages(self):
        # Can only disable controls *after* all pages are added!
        # Need to do this to ensure proper workflow
        for pageIndex in range(self.pageCount()):
            self.setNextEnabled(self.page(pageIndex), False)

    def __disableHelpButtons(self):
        for pageIndex in range(self.pageCount()):
            self.setHelpEnabled(self.page(pageIndex), False)


class WizardPage(QWidget, WarningHandler):
    def __init__(self, parent, title, data, errorLog):
        QWidget.__init__(self, parent)

        self.title = title
        self.data = data
        self.errorLog = errorLog

        self.hBoxLayout = QHBoxLayout(self, 0, 8)

        self.instructionsText = QTextBrowser(self)
        self.instructionsText.setPaletteBackgroundColor(QColor(255,255,255))
        self.instructionsText.setFrameShape(QLabel.StyledPanel)
        self.instructionsText.setFrameShadow(QLabel.Sunken)
        self.instructionsText.setMargin(2)
        self.instructionsText.setAlignment(QLabel.WordBreak | QLabel.AlignTop)
        self.instructionsText.setFixedWidth(150)
        self.instructionsText.setMinimumHeight(350)
        self.instructionsText.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.MinimumExpanding)
        self.hBoxLayout.add(self.instructionsText)

        self.vBoxLayout = QVBoxLayout(self.hBoxLayout)

    def setData(self, key, data):
        self.data[key] = data

    def getFileNames(self, location='.', nameFilter=''):
        return [str(fileName) for fileName in list(QDir(location).entryList(nameFilter))]

    def enableBack(self):
        self.emit(PYSIGNAL("enableBack"), (self, True))

    def disableBack(self):
        self.emit(PYSIGNAL("disableNext"), (self, False))

    def enableNext(self):
        self.emit(PYSIGNAL("enableNext"), (self, True))

    def disableNext(self):
        self.emit(PYSIGNAL("enableNext"), (self, False))

    def enableFinish(self):
        self.emit(PYSIGNAL("enableFinish"), (self, True))

    def disableFinish(self):
        self.emit(PYSIGNAL("enableFinish"), (self, False))


class SignInPage(WizardPage):
    def __init__(self, parent, title, data, errorLog, authHandler):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.instructionsText.setText('<p>An operator and two witnesses are '
        'required to proceed with the ballot reconciliation process.</p> '
        '<p>Select an operator from the provided list to input data and control '
        'the wizard.</p> <p>Also select two poll workers as witnesses from the '
        'provided list that will attest to the accuracy of the process.</p>'
        '<p>You cannot select the same person for two or more roles.</p>')

        self.authHandler = authHandler
        self.connect(self.authHandler, PYSIGNAL("allUsersLoggedIn"), self.enableNext)
        self.connect(self.authHandler, PYSIGNAL("allUsersLoggedIn"), self.notifyLogOutPage)

        self.operatorGroupBox = QGroupBox(1, Qt.Vertical, "Operator Sign In", self)
        self.operatorLoginBox = LoginBox(self.operatorGroupBox, "Operator Login Box", "Operator", self.authHandler)

        self.witnessGroupBox = QGroupBox(2, Qt.Vertical, "Witness Sign In", self)
        self.witnessOneLoginBox = LoginBox(self.witnessGroupBox, "Witness One Login Box", "Witness One", self.authHandler)
        self.witnessTwoLoginBox = LoginBox(self.witnessGroupBox, "Witness Two Login Box", "Witness Two", self.authHandler)

        # Prevent a user from being selected more than once. What a mess! There has to be a more elegant way...

        self.connect(self.operatorLoginBox, PYSIGNAL("updateNames"), self.witnessOneLoginBox.updateNameComboBox)
        self.connect(self.operatorLoginBox, PYSIGNAL("updateNames"), self.witnessTwoLoginBox.updateNameComboBox)

        self.connect(self.witnessOneLoginBox, PYSIGNAL("updateNames"), self.operatorLoginBox.updateNameComboBox)
        self.connect(self.witnessOneLoginBox, PYSIGNAL("updateNames"), self.witnessTwoLoginBox.updateNameComboBox)

        self.connect(self.witnessTwoLoginBox, PYSIGNAL("updateNames"), self.operatorLoginBox.updateNameComboBox)
        self.connect(self.witnessTwoLoginBox, PYSIGNAL("updateNames"), self.witnessOneLoginBox.updateNameComboBox)

        self.vBoxLayout.add(self.operatorGroupBox)
        self.vBoxLayout.add(self.witnessGroupBox)

    def notifyLogOutPage(self):
        self.emit(PYSIGNAL("allUsersLoggedIn"), ())


class SignOutPage(WizardPage):
    def __init__(self, parent, title, data, errorLog, authHandler):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.instructionsText.setText('<p>Once the reconciliation process is '
        'complete, each user involved must log themselves off.</p> <p>This will '
        'certify, sign, and timestamp the final results, which will enable them '
        'to be transferred to election headquarters.</p>')

        self.authHandler = authHandler
        self.connect(self.authHandler, PYSIGNAL("allUsersLoggedOut"), self.enableFinish)

        self.operatorGroupBox = QGroupBox(1, Qt.Vertical, "Operator Sign Out", self)
        self.operatorLogoutBox = LogoutBox(self.operatorGroupBox, "Operator", self.authHandler)
        self.connect(self.parent().wizardPage1, PYSIGNAL("allUsersLoggedIn"), self.operatorLogoutBox.updateUserName)

        self.witnessGroupBox = QGroupBox(2, Qt.Vertical, "Witness Sign Out", self)
        self.witnessOneLogoutBox = LogoutBox(self.witnessGroupBox, "Witness One", self.authHandler)
        self.connect(self.parent().wizardPage1, PYSIGNAL("allUsersLoggedIn"), self.witnessOneLogoutBox.updateUserName)
        self.witnessTwoLogoutBox = LogoutBox(self.witnessGroupBox, "Witness Two", self.authHandler)
        self.connect(self.parent().wizardPage1, PYSIGNAL("allUsersLoggedIn"), self.witnessTwoLogoutBox.updateUserName)

        self.vBoxLayout.add(self.operatorGroupBox)
        self.vBoxLayout.add(self.witnessGroupBox)


class ManualCountPage(WizardPage):
    def __init__(self, parent, title, data, errorLog):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.instructionsText.setText('<p>Remove the ballots from the ballot '
        'box.</p> <p>Keep the ballots face down and shuffle them.</p> <p>Count '
        'each of the paper ballots by hand, and input the total in the field '
        'provided.</p> <p>When done, finalize the count and proceed.</p>')

        self.warningLabel = WarningLabel("", self)
        self.vBoxLayout.addWidget(self.warningLabel)

        hBoxLayout = QHBoxLayout(self.vBoxLayout)
        self.ballotCountLabel = QLabel("Manual Ballot Count", self)
        self.ballotCountSpinBox = QSpinBox(0, 10000, 1, self)
        self.ballotCountSpinBox.setSizePolicy(QSizePolicy(QSizePolicy.Expanding, QSizePolicy.Minimum))
        self.connect(self.ballotCountSpinBox, SIGNAL("valueChanged(int)"), self.clearWarning)

        hBoxLayout.add(self.ballotCountLabel)
        hBoxLayout.add(self.ballotCountSpinBox)

        self.registerCountButton = QPushButton("Finalize Manual Ballot Count", self)
        self.registerCountButton.setToggleButton(True)
        self.vBoxLayout.addWidget(self.registerCountButton)
        self.connect(self.registerCountButton, SIGNAL("toggled(bool)"), self.checkState)

        spacer1 = QSpacerItem(25, 25, QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.vBoxLayout.addItem(spacer1)

    def checkState(self, isOn):
        if inDebugMode():
            print "[Debug] checkState() triggered, with value '%s' (%s)" % (isOn, type(isOn))
        if isOn:
            self.ballotCountSpinBox.setEnabled(False)
            countValue = self.ballotCountSpinBox.value()
            if countValue <= 0:
                self.showWarning("Cannot proceed if manual count value 0 or less.")
                self.registerCountButton.setOn(False)
                self.ballotCountSpinBox.setEnabled(True)
                if inDebugMode():
                    print "[Debug] Bad value for ballotCountSpinBox"
            else:
                self.setData('manualBallotCount', countValue)
                self.enableNext()
                if inDebugMode():
                    print "[Debug] Value OK. Enable Next button..."
        else:
            self.ballotCountSpinBox.setEnabled(True)
            self.disableNext()
            if inDebugMode():
                    print "[Debug] Toggled off. Disable Next button..."


class ScanCountPage(WizardPage):
    def __init__(self, parent, title, data, errorLog):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.instructionsText.setText('<p>Stack the ballots and place them in '
        'the scan tray.<p> <p>Scan the barcode for the ballot on top then place '
        'the scanned ballot in another pile in the tray.</p> <p>Repeat until '
        'all the ballots have been scanned.</p> <p>When done, finalize the '
        'count and proceed.</p>')

        self.reader = BallotReader(self.data)
        self.writer = BallotWriter()

        self.scanCount = 0
        self.scanCountLabel = InfoLabel("Current Ballot Count: <b>0</b>", self)

        self.ballotScanGroup = QGroupBox(4, Qt.Vertical, "Ballot Scan", self)
        self.warningLabel = WarningLabel("", self.ballotScanGroup)
        self.ballotScanInstructionsLabel = QLabel("Scan ballot barcode when the field below is green.", self.ballotScanGroup)
        self.scannerInputLine = InputLine(self.ballotScanGroup)
        self.scannerInputLine.setValidator(BarcodeValidator(self))
        self.connect(self.scannerInputLine, SIGNAL("returnPressed()"), self.addBallot)
        self.ballotScanPushButton = QPushButton("Add Ballot", self.ballotScanGroup)
        self.connect(self.ballotScanPushButton, SIGNAL("clicked()"), self.addBallot)


        self.scannedBallotsGroup = QGroupBox(1, Qt.Vertical, "Scanned Ballots", self)
        self.scannedBallotTable = Table(self.scannedBallotsGroup)
        self.scannedBallotTable.setNumCols(self.scannedBallotTable.numCols() + 1)
        self.scannedBallotTable.horizontalHeader().setLabel(self.scannedBallotTable.numCols() - 1, "Ballot ID")
        self.scannedBallotTable.setNumRows(0)

        self.registerCountButton = QPushButton("Finalize Scanned Ballot Count", self)
        self.registerCountButton.setToggleButton(True)
        self.connect(self.registerCountButton, SIGNAL("toggled(bool)"), self.checkState)

        self.vBoxLayout.add(self.scanCountLabel)
        self.vBoxLayout.add(self.ballotScanGroup)
        self.vBoxLayout.add(self.scannedBallotsGroup)
        self.vBoxLayout.add(self.registerCountButton)

    def addBallot(self):
        if self.scannerInputLine.hasAcceptableInput():
            try:
                barcode = str(self.scannerInputLine.text()).strip()
                ballot = self.reader.readBarcodeInput(barcode)
                try:
                    fileName = self.writer.writeXMLFile(ballot[0], ballot[1])
                    self.scannedBallotTable.insertRows(0)
                    self.scannedBallotTable.setText(0, 0, fileName[-8:-4])
                    self.scannedBallotTable.adjustColumn(0)
                    qApp.beep()  # System bell ring
                    self.scanCount += 1
                    self.scanCountLabel.setText("Current Ballot Count: <b>%i</b>" % self.scannedBallotTable.numRows())
                    self.clearWarning()
                    self.scannerInputLine.clear()
                except BallotExistsError, e:
                    self.showWarning("Ballot %s already exists." % e.fileName)
            except ValueError:
                self.showWarning("Invalid encoding. Check barcode")
        else:
            self.showWarning("Invalid barcode format. Please check ballot.")

    def checkState(self, isOn):
        # For testing, we use whatever we find in ./scanned already, to skip data entry
        if '-debug' in sys.argv:
            fileNames = os.listdir('scanned')
            autoCount = len(fileNames)
            print "Using %s as value for 'scannedBallotCount'" % autoCount
            for fileName in fileNames:
                self.scannedBallotTable.insertRows(0)
                self.scannedBallotTable.setText(0, 0, fileName[-8:-4])
                self.scannedBallotTable.adjustColumn(0)
            self.setData('scannedBallotCount', autoCount)
            self.scanCountLabel.setText("Current Ballot Count: <b>%i</b> (auto-loaded)" % autoCount)
        else:
            if isOn:
                self.ballotScanGroup.setEnabled(False)
                self.scannedBallotsGroup.setEnabled(False)
                if self.scanCount < 1:
                    self.ballotScanGroup.setEnabled(True)
                    self.scannedBallotsGroup.setEnabled(True)
                    self.registerCountButton.setOn(False)
                    self.showWarning("Cannot proceed if scan count value 0 or less.")
                else:
                    self.setData('scannedBallotCount', self.scanCount)
                    self.enableNext()
            else:
                self.ballotScanGroup.setEnabled(True)
                self.scannedBallotsGroup.setEnabled(True)
                self.disableNext()


class LoadDataPage(WizardPage):
    def __init__(self, parent, title, data, errorLog):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.instructionsText.setText('<p>One by one, insert the data disks '
        'from the vote stations and load the ballot data.</p> <p>You must '
        'load the data from all registered vote stations to proceed.</p>')

        self.loadVoteStationInfo()

        self.loadVoteStationDataGroup = QGroupBox(5, Qt.Vertical, "Load Vote Station Data", self)
        self.warningLabel = WarningLabel(self.loadVoteStationDataGroup)
        hBox1 = QHBox(self.loadVoteStationDataGroup)
        hBox1.setSpacing(6)
        self.progressLabel = QLabel("Data Location", hBox1)
        self.voteStationList = QComboBox(hBox1)
        self.voteStationList.setSizePolicy(QSizePolicy(QSizePolicy.Expanding, QSizePolicy.Preferred))
        self.voteStationList.insertStrList(['/dev/cdrom', '/media/cdrom'])  # What should we provide here?
        self.voteStationList.setEditable(True)
        hBox2 = QHBox(self.loadVoteStationDataGroup)
        hBox2.setSpacing(6)
        self.progressLabel = QLabel("Progress", hBox2)
        self.loadDataProgressBar = QProgressBar(hBox2)
        self.loadDataPushButton = QPushButton("Load Vote Station Data Disk", self.loadVoteStationDataGroup)
        self.connect(self.loadDataPushButton, SIGNAL("clicked()"), self.loadData)

        self.voteStationStatusGroup = QGroupBox(1, Qt.Vertical, "Vote Station Status", self)
        self.voteStationTable = Table(self.voteStationStatusGroup)
        self.voteStationTable.setNumCols(self.voteStationTable.numCols() + 3)
        self.voteStationTable.horizontalHeader().setLabel(self.voteStationTable.numCols() - 3, "Serial")
        self.voteStationTable.horizontalHeader().setLabel(self.voteStationTable.numCols() - 2, "Status")
        self.voteStationTable.horizontalHeader().setLabel(self.voteStationTable.numCols() - 1, "Ballots")
        self.voteStationTable.setColumnStretchable(0, True)
        self.voteStationTable.setColumnStretchable(1, True)
        self.voteStationTable.setColumnStretchable(2, True)
        self.voteStationTable.setNumRows(0)
        self.populateVoteStationTable()

        self.vBoxLayout.add(self.loadVoteStationDataGroup)
        self.vBoxLayout.add(self.voteStationStatusGroup)

    def loadVoteStationInfo(self):
        voteStationInfoFile = QFile("votestations.txt")  # Checked for on start-up
        voteStationInfoFile.open(IO_ReadOnly)
        self.voteStationSerials = str(QTextStream(voteStationInfoFile).read()).strip().split('\n')
        self.voteStationSerials.sort()
        self.diskStatus = dict([(serial, "Not Loaded") for serial in self.voteStationSerials if serial])
        self.diskCount = dict([(serial, 0) for serial in self.voteStationSerials])

    def populateVoteStationTable(self):
        self.serialCellMappings = {}
        for serial in self.voteStationSerials:
            self.voteStationTable.insertRows(self.voteStationTable.numRows())
            row = self.voteStationTable.numRows() - 1
            self.voteStationTable.setText(row, 0, serial)
            self.voteStationTable.setText(row, 1, "Not Loaded")
            self.voteStationTable.setText(row, 2, "0")
            self.serialCellMappings[serial] = row

    def updateTableRow(self, serial, status, count):
        row = self.serialCellMappings[serial]
        self.voteStationTable.setText(row, 1, status)
        self.voteStationTable.setText(row, 2, count)

    def mountDevice(self, path):
        print 'Mounting data from %s' % path
        self.devicePath = path  # Set this to reference it on unmount
        os.system("mount %s" % path)

    def unmountDevice(self):
        print 'Unmounting data from %s' % self.devicePath
        os.system("umount %s" % self.devicePath)

    def registerDataDisk(self, serial, status):
        self.diskStatus[serial] = status
        if self.diskStatus.values() == ['Loaded' for value in self.diskStatus]:
            self.loadVoteStationDataGroup.setEnabled(False)
            self.setData('voteStationTotals', self.diskCount)
            self.setData('storedBallotCount', sum(self.diskCount.values()))
            self.enableNext()

    def loadData(self):
        self.clearWarning()
        location = str(self.voteStationList.currentText())
        if location in ('/dev/cdrom', '/media/cdrom'):
            self.mountDevice(location)

        self.loadDataProgressBar.reset()

        serialFile = QFile(location + "/serial.txt")
        if serialFile.exists():
            serialFile.open(IO_ReadOnly)
            serial = str(QTextStream(serialFile).read()).strip()
            ballotFileNames = self.getFileNames(location, '*.xml')
            ballotCount = len(ballotFileNames)
            self.loadDataProgressBar.setTotalSteps(ballotCount)

            for ballotFileName in ballotFileNames:
                ballotFileName = str(ballotFileName)
                ballotInputFile = QFile(location + '/' + ballotFileName)
                ballotInputFile.open(IO_ReadOnly)
                ballotInputFileContents = str(QTextStream(ballotInputFile).read())
                ballotOutputFile = QFile('stored/' + ballotFileName)
                ballotOutputFile.open(IO_Raw | IO_WriteOnly)
                ballotOutputFile.writeBlock(ballotInputFileContents)
                ballotInputFile.close()
                ballotOutputFile.close()
                self.loadDataProgressBar.setProgress(self.loadDataProgressBar.progress() + 1)

            self.updateTableRow(serial, 'Loaded', str(ballotCount))
            self.diskCount[serial] = ballotCount
            self.registerDataDisk(serial, 'Loaded')
        else:
            self.showWarning("%s not a valid source." % location)

        if location in ('/dev/cdrom', '/media/cdrom'):
            self.unmountDevice()


class RegisterBallotsPage(WizardPage):
    def __init__(self, parent, title, data, errorLog):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.disableNext()
        self.ballotCountLabel = InfoLabel("Current Ballot Count: <b>0</b>", self)

        self.registerBallotGroup = QGroupBox(3, Qt.Vertical, "Register A Ballot", self)
        self.warningLabel = WarningLabel("", self.registerBallotGroup)
        hBox = QHBox(self.registerBallotGroup)
        hBox.setSpacing(6)
        self.registerBallotLabel = QLabel("Ballot ID", hBox)
        self.registerBallotInputLine = InputLine(hBox)
        self.registerBallotInputLine.setValidator(QRegExpValidator(QRegExp("[0-9]{4}"), self))
        self.connect(self.registerBallotInputLine, SIGNAL("returnPressed()"), self.addBallot)
        self.registerBallotPushButton = QPushButton("Add Ballot ID", self.registerBallotGroup)
        self.connect(self.registerBallotPushButton, SIGNAL("clicked()"), self.addBallot)

        self.registeredBallotsGroup = QGroupBox(2, Qt.Vertical, "Registered Ballots", self)
        self.registeredBallotsTable = Table(self.registeredBallotsGroup)
        self.registeredBallotsTable.setNumCols(self.registeredBallotsTable.numCols() + 1)
        self.registeredBallotsTable.horizontalHeader().setLabel(self.registeredBallotsTable.numCols() - 1, "Ballot ID")
        self.registeredBallotsTable.setNumRows(0)
        self.registeredBallotsTable.setReadOnly(False)
        self.removeBallotButton = QPushButton("Remove Selected Ballot", self.registeredBallotsGroup)
        self.connect(self.removeBallotButton, SIGNAL("clicked()"), self.removeBallot)

        self.registerCountButton = QPushButton("Finalize Ballot Registration", self)
        self.registerCountButton.setToggleType(QButton.Toggle)
        self.connect(self.registerCountButton, SIGNAL("clicked()"), self.finalizeCheck)

        self.vBoxLayout.add(self.ballotCountLabel)
        self.vBoxLayout.add(self.registerBallotGroup)
        self.vBoxLayout.add(self.registeredBallotsGroup)
        self.vBoxLayout.add(self.registerCountButton)

    def ballotExists(self, ballotId):
        ballotFileNames = [str(x) for x in list(QDir('scanned').entryList('*.xml'))]
        for ballot in ballotFileNames:
            if ballot[-8:-4] == ballotId:
                return True

    def addBallot(self):
        if self.registerBallotInputLine.hasAcceptableInput():
            ballotId = str(self.registerBallotInputLine.text())
            if self.isDuplicate(ballotId):
                self.showWarning("Ballot ID# %s already entered." % ballotId)
            else:
                if self.ballotExists(ballotId):
                    if self.registerBallot(ballotId):
                        self.registeredBallotsTable.insertRows(0)
                        self.registeredBallotsTable.setText(0, 0, ballotId)
                        self.registeredBallotsTable.adjustColumn(0)
                        self.ballotCountLabel.setText("Current Ballot Count: <b>%i</b>"
                            % self.registeredBallotsTable.numRows())
                        self.registerBallotInputLine.clear()
                        self.registerBallotInputLine.setFocus()
                        self.clearWarning()
                else:
                    self.showWarning("Ballot with ID# %s not found!" % ballotId)
        else:
            self.showWarning("Invalid input. Please try again.")

    def removeBallot(self):
        column = self.registeredBallotsTable.currentColumn()
        row = self.registeredBallotsTable.currentRow()
        ballotId = self.registeredBallotsTable.text(row, column)
        self.registeredBallotsTable.removeRow(row)
        self.ballotCountLabel.setText("Current Ballot Count: <b>%i</b>"
            % self.registeredBallotsTable.numRows())
        self.unregisterBallot(ballotId)

    def finalizeCheck(self):
        if self.registerCountButton.state() == QButton.On:
            self.registerBallotGroup.setEnabled(False)
            self.enableNext()
        elif self.registerCountButton.state() == QButton.Off:
            self.registerBallotGroup.setEnabled(True)
            self.disableNext()


class RegisterTestBallotsPage(RegisterBallotsPage):
    def __init__(self, parent, title, data, errorLog):
        RegisterBallotsPage.__init__(self, parent, title, data, errorLog)

        self.data['testBallotIds'] = []  # we set this directly

        self.instructionsText.setText("<p>Enter the ballot ID number for each "
            "of the test ballots that were printed on start up.</p> <p>When "
            "done, finalize the registration and proceed.")
        self.registerBallotGroup.setTitle("Register A Test Ballot")
        self.registerBallotPushButton.setText("Add Test Ballot ID")
        self.registeredBallotsGroup.setTitle("Registered Test Ballots")
        self.registerCountButton.setText("Finalize Test Ballot Registration")

    def isDuplicate(self, ballotId):
        if ballotId in self.data['testBallotIds']:
            return True
        else:
            return False

    def registerBallot(self, ballotId):
        self.data['testBallotIds'].append(ballotId)
        return True

    def unregisterBallot(self, ballotId):
        self.data['testBallotIds'].remove(ballotId)


class RegisterSpoiledBallotsPage(RegisterBallotsPage):
    def __init__(self, parent, title, data, errorLog):
        RegisterBallotsPage.__init__(self, parent, title, data, errorLog)

        self.data['spoiledBallotIds'] = []  # we set this directly

        self.instructionsText.setText("<p>Enter the ballot ID number for each of "
            "the spoiled ballots that were printed on start up.</p> <p>When done, "
            "finalize the registration and proceed.")
        self.registerBallotGroup.setTitle("Register A Spoiled Ballot")
        self.registerBallotPushButton.setText("Add Spoiled Ballot ID")
        self.registeredBallotsGroup.setTitle("Registered Spoiled Ballots")
        self.registerCountButton.setText("Finalize Spoiled Ballot Registration")

    def isDuplicate(self, ballotId):
        if ballotId in self.data['spoiledBallotIds']:
            return True
        else:
            return False

    def registerBallot(self, ballotId):
        if ballotId in self.data['testBallotIds']:
            self.showWarning("Ballot ID# %s already a test ballot." % ballotId)
            return False
        else:
            self.data['spoiledBallotIds'].append(ballotId)
            return True

    def unregisterBallot(self, ballotId):
        self.data['spoiledBallotIds'].remove(ballotId)

class CompareBallotsPage(WizardPage):
    def __init__(self, parent, title, data, errorLog):
        WizardPage.__init__(self, parent, title, data, errorLog)

        self.instructionsText.setText("<p>You are now ready to perform the "
            "reconciliation process.</p> <p>Once done, a report will be generated "
            "and can be printed or saved to disk.</p>")

        self.compareBallotsPushButton = QPushButton("Begin Ballot Reconciliation", self)
        self.connect(self.compareBallotsPushButton, SIGNAL("clicked()"), self.reconcileBallots)
        hBox1 = QHBox(self)
        hBox1.setSpacing(6)
        self.compareBallotsProgressLabel = QLabel("Progress", hBox1)
        self.compareBallotsProgressBar = QProgressBar(hBox1)

        self.resultsGroup = QGroupBox(2, Qt.Vertical, "Results", self)
        self.resultsTabWidget = QTabWidget(self.resultsGroup)
        self.summaryTab = QWidget(self.resultsTabWidget)
        gridLayout1 = QGridLayout(self.summaryTab, 1, 1, 2, 0)
        self.resultStatisticsListView = QListView(self.summaryTab)
        self.resultStatisticsListView.setAllColumnsShowFocus(True)
        self.resultStatisticsListView.addColumn("Count")
        self.resultStatisticsListView.addColumn("Type")
        self.resultStatisticsListView.setSorting(-1)
        self.resultStatisticsListView.setColumnAlignment(0, Qt.AlignRight)
        self.processedBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Total Ballots Processed")
        self.matchedBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Matched Ballots")
        self.unmatchedBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Unmatched Ballots")
        self.votedBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Voted Ballots")
        self.testBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Test Ballots")
        self.spoiledBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Spoiled Ballots")
        self.missingBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Missing Ballots")
        self.scannedBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Scanned Ballot Count Total")
        self.manualBallotsResult = QListViewItem(self.resultStatisticsListView, "0", "Manual Ballot Count Total")
        self.errorResult = QListViewItem(self.resultStatisticsListView, "0", "Errors/Warnings")
        gridLayout1.addWidget(self.resultStatisticsListView, 0, 0)
        self.resultsTabWidget.insertTab(self.summaryTab, "Summary")

        self.votesTab = QWidget(self.resultsTabWidget)
        gridLayout2 = QGridLayout(self.votesTab, 2, 2, 2, 0)
        self.expandTotalsButton = QPushButton("Expand All Totals", self.votesTab)
        self.connect(self.expandTotalsButton, SIGNAL("clicked()"), self.expandAllBranches)
        gridLayout2.addWidget(self.expandTotalsButton, 0, 0)
        self.collapseTotalsButton = QPushButton("Collapse All Totals", self.votesTab)
        self.connect(self.collapseTotalsButton, SIGNAL("clicked()"), self.collapseAllBranches)
        gridLayout2.addWidget(self.collapseTotalsButton, 0, 1)
        self.voteTotalsListView = QListView(self.votesTab)
        self.voteTotalsListView.setAllColumnsShowFocus(True)
#         self.voteTotalsListView.setSelectionMode(QListView.NoSelection)
        self.voteTotalsListView.addColumn("Candidates")
        self.voteTotalsListView.addColumn("Votes")
        self.voteTotalsListView.setRootIsDecorated(True)
        self.voteTotalsListView.setShowSortIndicator(True)
        self.voteTotalsListView.setColumnWidthMode(0, QListView.Maximum)
        gridLayout2.addMultiCellWidget(self.voteTotalsListView, 1, 1, 0, 1)
        self.resultsTabWidget.insertTab(self.votesTab, "Vote Totals")

        self.errorsTab = QWidget(self.resultsTabWidget)
        gridLayout3 = QGridLayout(self.errorsTab, 1, 1, 2, 0)
        self.errorsTable = Table(self.errorsTab)
        self.errorsTable.setNumCols(self.errorsTable.numCols() + 1)
        self.errorsTable.horizontalHeader().setLabel(0, "Description")
        self.errorsTable.setNumRows(0)
        gridLayout3.addWidget(self.errorsTable, 0, 0)
        self.resultsTabWidget.insertTab(self.errorsTab, "Errors/Warnings")

        hBox2 = QHBox(self.resultsGroup)
        hBox2.setSpacing(6)
        self.saveReportPushButton = QPushButton("Save Report...", hBox2)
        self.connect(self.saveReportPushButton, SIGNAL("clicked()"),
            self.generateReportPrintOut)
        self.printReportPushButton = QPushButton("Print Report...", hBox2)

        self.vBoxLayout.add(self.compareBallotsPushButton)
        self.vBoxLayout.add(hBox1)
        self.vBoxLayout.add(self.resultsGroup)

        self.resultsGroup.setEnabled(False)

#     def getErrorList(self):
#         errorLogFile = QFile('Ballot Error Log.txt')
#         # Needs some work...
#         if errorLogFile.exists():
#             errorLogFile.open(IO_ReadOnly)
#             errors = str(errorLogFile.readAll()).split('\n')
#             print errors
#             errorLogFile.close()
#             if errors == ['']:
#                 return []
#             else:
#                 return errors
#         else:
#             return []

    def generateResultsSummary(self):
        # Have to set these first to use below
        self.data['invalidBallotCount'] = len(self.data['testBallotIds']) + len(self.data['spoiledBallotIds'])
        errors = self.data['ballotErrors']

        # make 'missingBallotsCount' expr. legible
        i = self.data['invalidBallotCount']
        d = self.data['storedBallotCount']
        p = self.data['scannedBallotCount']
        m = self.data['manualBallotCount']

        self.data['missingBallotCount'] = abs(((d - i) - (m - i)) - ((d - i) - (p - i)))  # Needs to documented
                                                                                          # in the spec
        self.data['votedBallotCount'] = self.data['storedBallotCount'] - len(self.data['testBallotIds'])

        self.processedBallotsResult.setText(0, str(self.data['storedBallotCount']))
        self.matchedBallotsResult.setText(0, str(len(self.data['matchedBallots'])))
        self.unmatchedBallotsResult.setText(0, str(len(self.data['unmatchedBallots'])))
        self.votedBallotsResult.setText(0, str(self.data['votedBallotCount']))
        self.missingBallotsResult.setText(0, str(self.data['missingBallotCount']))
        self.testBallotsResult.setText(0, str(len(self.data['testBallotIds'])))
        self.spoiledBallotsResult.setText(0, str(len(self.data['spoiledBallotIds'])))
        self.scannedBallotsResult.setText(0, str(self.data['scannedBallotCount']))
        self.manualBallotsResult.setText(0, str(self.data['manualBallotCount']))
        self.errorResult.setText(0, str(len(errors)))

        if errors:
            for error in errors:
                self.errorsTable.insertRows(0)
                self.errorsTable.setText(0, 0, error.strip())
                self.errorsTable.adjustColumn(0)

    def generateReportPrintOut(self):
        reportFile = QFile('Final Report.txt')
        reportFile.open(IO_Raw | IO_WriteOnly)
        data = self.data
        template = """%s, %s - Precinct %s Final Report
%s  %s

Quick Statistical Summary
-------------------------------------------------------------------------------

%3d Total ballots processed
%3d Manual ballot count
%3d Voted ballot(s)
%3d Test ballot(s)
%3d Spoiled ballot(s)
%3d Matched ballot(s)
%3d Unmatched ballot(s)
%3d Orphaned ballot(s)


Test Ballots (%s)
-------------------------------------------------------------------------------

%s


Spoiled Ballots (%s)
-------------------------------------------------------------------------------

%s


Matched Ballots (%s)
-------------------------------------------------------------------------------

%s


Unmatched Ballots (%s)
-------------------------------------------------------------------------------

%s

Missing Ballots (%s)
-------------------------------------------------------------------------------

%s


Candidate Precinct Totals
-------------------------------------------------------------------------------
Total Votes | Candidate Name
-------------------------------------------------------------------------------
%s """ % (data['county'], data['state'], data['precinct'], data['date'].strftime('%m-%d-%Y'),
       time.strftime('%I:%m %p'), int(data['storedBallotCount']), int(data['manualBallotCount']),
       int(data['votedBallotCount']), len(data['testBallotIds']), len(data['spoiledBallotIds']),
       len(data['matchedBallots']), len(data['unmatchedBallots']), len(data['missingBallots']),
       len(data['testBallotIds']), ''.join([i + '\n' for i in data['testBallotIds']]),
       len(data['spoiledBallotIds']), ''.join([i + '\n' for i in data['spoiledBallotIds']]),
       len(data['matchedBallots']), ''.join([i + '\n' for i in data['matchedBallots']]),
       len(data['unmatchedBallots']), ''.join([i + '\n' for i in data['unmatchedBallots']]),
       len(data['missingBallots']), ''.join([i + '\n' for i in data['missingBallots']]),
       ''.join(['%11d   %s (%s)\n' % (race[1][candidate], candidate, race[0])
           for race in data['candidateTotals'].items() for candidate in race[1]]))
        reportFile.writeBlock(str(template))  # We get unicode from the XML, must convert
        reportFile.close()

    def tallyBallot(self, ballot):
        results = []
        for race in ballot.contest:
            if isinstance(race.selection, list):
                for seat in race.selection:
                    if hasattr(seat, 'name'):
                        results.append((seat.name, seat.PCDATA))
                    else:
                        # used to catch STV races (County Commissioner)
                        # is it OK that we aren't tracking rankings?
                        results.append((race.name, seat.PCDATA))
            else:
                results.append((race.name, race.selection.PCDATA))

        for vote in results:
            candidateTotals = self.data['candidateTotals']
            if candidateTotals[vote[0]].has_key(vote[1]):
                candidateTotals[vote[0]][vote[1]] += 1
            else:
                candidateTotals[vote[0]][vote[1]] = 1

    def listCandidateVoteTotals(self):
        self.branches = []
        for race in self.data['candidateTotals'].items():
            branch = QListViewItem(self.voteTotalsListView, race[0])
            self.branches.append(branch)
            for candidate in race[1].items():
                node = QListViewItem(branch, candidate[0], str(candidate[1]))
        self.voteTotalsListView.setResizeMode(QListView.LastColumn)

    def expandAllBranches(self):
        for branch in self.branches:
            self.voteTotalsListView.setOpen(branch, True)

    def collapseAllBranches(self):
        for branch in self.branches:
            self.voteTotalsListView.setOpen(branch, False)

    def reconcileBallots(self):
        ballotFileNames = self.getFileNames('stored/', '*.xml')
        self.compareBallotsProgressBar.reset()
        self.compareBallotsProgressBar.setTotalSteps(len(ballotFileNames))
#         ballotErrorLogFile = QFile('Ballot Error Log.txt')
#         ballotErrorLogFile.open(IO_WriteOnly)  # Ensure this clears before writing
        # Make sure all processing values are reset if we need to run again
        self.data['matchedBallots'] = []
        self.data['unmatchedBallots'] = []
        self.data['missingBallots'] = []
        self.data['ballotErrors'] = []
        self.data['candidateTotals'] = {'Attorney General': {},
                                        'Cat Catcher': {},
                                        'Commis. of Education': {},
                                        'County Commissioner': {},
                                        'Health care initiative': {},
                                        'President': {},
                                        'Vice President': {},
                                        'Senator': {},
                                        'State Assembly': {},
                                        'State Senate': {},
                                        'Term limits': {},
                                        'Transportation Initiative': {},
                                        'Treasurer': {},
                                        'U.S. Representative': {}}
        # We'll merge the test and spoiled ballots to check against during tabulation
        excludedBallots = self.data['testBallotIds'][:]  # We should check, but not tabulate test ballots
        excludedBallots.extend(self.data['spoiledBallotIds'][:])  # Should we match spoiled ballots?

        for ballotFileName in ballotFileNames:
            try:
                storedBallot = make_instance('stored/' + ballotFileName)
                # We adjust the filename to match the 'b' prefix on scanned EBIs
                scannedBallot = make_instance('scanned/' + 'b' + ballotFileName[1:])
                print "Matching %s with %s" % ('stored/' + ballotFileName,
                    'scanned/' + 'b' + ballotFileName[1:])

                if storedBallot == scannedBallot:  # Compare XML objects
                    self.data['matchedBallots'].append(ballotFileName)
                    if ballotFileName[-8:-4] not in excludedBallots:
                        print "%s can be tallied" % ballotFileName[-8:-4]
                        self.tallyBallot(storedBallot)  # Ballot has to match to be tabulated
                        ballotFile = QFile('verified/' + ballotFileName[2:])
                        ballotFile.open(IO_Raw | IO_WriteOnly)
                        ballotFile.close()
                    else:
                        print "%s in excludedBallots (%s)" % (ballotFileName[-8:-4],
                            excludedBallots.index(ballotFileName[-8:-4]))
                else:
                    self.data['unmatchedBallots'].append(ballotFileName)
                    self.data['ballotErrors'].append("Ballot %s unmatched\n" % ballotFileName[2:])
                    print "File problem: %s unmatched" % ballotFileName[2:]

            except IOError:
                self.data['missingBallots'].append(ballotFileName)
                self.data['ballotErrors'].append("Ballot %s not found\n" % ballotFileName)
                print "File problem: %s read error" % ballotFileName[2:]

            self.compareBallotsProgressBar.setProgress(self.compareBallotsProgressBar.progress() + 1)

        self.resultsGroup.setEnabled(True)
        self.listCandidateVoteTotals()
        self.generateResultsSummary()
        self.enableNext()


def checkEnvironment():
    fileHandler = QFile()
    dirHandler = QDir()

    print 'Checking environment...'
    if inDebugMode():
        print ('Using the following libraries:\n'
               '-Python %s\n-Qt %s\n-PyQt %s\n-SIP %s' % (sys.version[:5],
               PYQT_VERSION_STR, qVersion(), commands.getoutput('sip -V')))

    if fileHandler.exists('acl.txt'):
        print 'acl.txt found'
    else:
        raise IOError, 'acl.txt not found... quitting.'

    if fileHandler.exists('votestations.txt'):
        print 'votestations.txt found'
    else:
        raise IOError, 'votestations.txt not found... quitting.'

    if dirHandler.exists('scanned'):
        print 'scanned/ found'
    else:
        print 'scanned/ not found... creating.'
        dirHandler.mkdir('scanned')

    if dirHandler.exists('stored'):
        print 'stored/ found'
    else:
        print 'stored/ not found... creating.'
        dirHandler.mkdir('stored')

    if dirHandler.exists('verified'):
        print 'verified/ found'
    else:
        print 'verified/ not found... creating.'
        dirHandler.mkdir('verified')

    print 'Success. Loading BRP system...'

def finalCleanup():
    print "Application closed. Quitting..."
    sys.exit(0)

def main(args):
    checkEnvironment()
    app = QApplication(args)
    app.setStyle('windows')  # we'll hard-code Win32 UI style
    wizard = BRPWizard()
    print 'Loaded. Initializing application...'
    app.setMainWidget(wizard)
    wizard.show()
    app.connect(app, SIGNAL("lastWindowClosed()"), app, SLOT("quit()"))
    app.connect(app, SIGNAL("lastWindowClosed()"), finalCleanup)
    app.exec_loop()

if __name__ == "__main__":
    main(sys.argv)