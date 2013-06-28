import sys
from qt import *
from qttable import *


class BRPWizard(QWizard):
    def __init__(self, *args):
        QWizard.__init__(self, *args)

        font = QFont(self.font())
        font.setPointSize(12)
        font.setBold(True)
        self.setTitleFont(font)

        self.wizardPage1 = SignInPage(self, "Ballot Verification Sign In")
        self.addPage(self.wizardPage1, self.wizardPage1.title)

        self.wizardPage2 = ManualCountPage(self, "Paper Ballot Manual Count")
        self.addPage(self.wizardPage2, self.wizardPage2.title)

        self.wizardPage3 = ScanCountPage(self, "Paper Ballot Scan Count")
        self.addPage(self.wizardPage3, self.wizardPage3.title)

        self.wizardPage4 = LoadDataPage(self, "Load Vote Station Data")
        self.addPage(self.wizardPage4, self.wizardPage4.title)

        self.wizardPage5 = RegisterTestBallotsPage(self, "Register Test Ballots")
        self.addPage(self.wizardPage5, self.wizardPage5.title)

        self.wizardPage6 = RegisterSpoiledBallotsPage(self, "Register Spoiled Ballots")
        self.addPage(self.wizardPage6, self.wizardPage6.title)

        self.wizardPage7 = CompareBallotsPage(self, "Compare Ballots")
        self.addPage(self.wizardPage7, self.wizardPage7.title)

        self.wizardPage8 = SignOutPage(self, "Ballot Verification Sign Out")
        self.addPage(self.wizardPage8, self.wizardPage8.title)

        self.resize(QSize(500, 400).expandedTo(self.minimumSizeHint()))
        self.clearWState(Qt.WState_Polished)


class WizardPage(QWidget):
    def __init__(self, parent, title):
        QWidget.__init__(self, parent)
        self.title = title

        self.hBoxLayout = QHBoxLayout(self, 0, 8)

        self.instructionsLabel = QLabel(self)
        self.instructionsLabel.setPaletteBackgroundColor(QColor(255,255,255))
        self.instructionsLabel.setFrameShape(QLabel.StyledPanel)
        self.instructionsLabel.setFrameShadow(QLabel.Sunken)
        self.instructionsLabel.setMargin(4)
        self.instructionsLabel.setAlignment(QLabel.WordBreak | QLabel.AlignTop)
        self.setMinimumSize(QSize(150, 300))
        self.instructionsLabel.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Minimum)
        self.hBoxLayout.add(self.instructionsLabel)

        self.vBoxLayout = QVBoxLayout(self.hBoxLayout)


class AuthenticationPage(WizardPage):
    def __init__(self, parent, title):
        WizardPage.__init__(self, parent, title)

        self.operatorGroupBox = QGroupBox(2, Qt.Vertical, "Operator", self)
        self.operatorNameLabel = QLabel("Operator: &lt;not signed in&gt;", self.operatorGroupBox)
        self.operatorLoginButton = QPushButton("Operator Button", self.operatorGroupBox)

        self.witnessGroupBox = QGroupBox(5, Qt.Vertical, "Witness", self)
        self.witnessOneNameLabel = QLabel("Witness One: &lt;not signed in&gt;", self.witnessGroupBox)
        self.witnessOneLoginButton = QPushButton("Witness One Button", self.witnessGroupBox)
        #self.witnessGroupBox.addSpace(100)  # why won't this work?
        self.witnessTwoNameLabel = QLabel("Witness Two: &lt;not signed in&gt;", self.witnessGroupBox)
        self.witnessTwoLoginButton = QPushButton("Witness Two Button", self.witnessGroupBox)

        self.vBoxLayout.add(self.operatorGroupBox)
        self.vBoxLayout.add(self.witnessGroupBox)


class SignInPage(AuthenticationPage):
    def __init__(self, parent, title):
        AuthenticationPage.__init__(self, parent, title)
        self.instructionsLabel.setText("Two witnesses are required to proceed with the ballot \
reconciliation process. Select two poll workers from the provided list that will attest to the accuracy of the process.")
        self.operatorGroupBox.setTitle("Operator Sign In")
        self.operatorLoginButton.setText("Log In As Operator")
        self.witnessGroupBox.setTitle("Witnesses Sign In")
        self.witnessOneLoginButton.setText("Log In As Witness One")
        self.witnessTwoLoginButton.setText("Log In As Witness Two")


class SignOutPage(AuthenticationPage):
    def __init__(self, parent, title):
        AuthenticationPage.__init__(self, parent, title)
        self.instructionsLabel.setText("Once the reconciliation process is complete, have users involved log off. This will \
certify, sign, and timestamp the final results.")
        self.operatorGroupBox.setTitle("Operator Sign Out")
        self.operatorLoginButton.setText("Log Out Operator")
        self.witnessGroupBox.setTitle("Witnesses Sign Out")
        self.witnessOneLoginButton.setText("Log Out Witness One")
        self.witnessTwoLoginButton.setText("Log Out Witness Two")


class ManualCountPage(WizardPage):
    def __init__(self, parent, title):
        WizardPage.__init__(self, parent, title)
        self.instructionsLabel.setText("<p>Remove the ballots from the ballot box. Keep the ballots face down and shuffle \
them.</p> <p>Count each of the paper ballots by hand, and input the total in the field provided.</p>")

        hBoxLayout = QHBoxLayout(self.vBoxLayout)
        ballotCountLabel = QLabel("Manual Ballot Count", self)
        ballotCountSpinBox = QSpinBox(self)

        hBoxLayout.add(ballotCountLabel)
        hBoxLayout.add(ballotCountSpinBox)


class ScanCountPage(WizardPage):
    def __init__(self, parent, title):
        WizardPage.__init__(self, parent, title)
        self.instructionsLabel.setText("Stack the ballots and place them in the scan tray. Scan the barcode for the ballot on \
top then place the scanned ballot in another pile in the tray. Repeat until all the ballots have been scanned.")
        self.scanCountLabel = InfoLabel("Current Ballot Count: <b>0</b>", self)

        self.ballotScanGroup = QGroupBox(3, Qt.Vertical, "Ballot Scan", self)
        self.ballotScanInstructionsLabel = QLabel("Scan ballot barcode when the field below is green.",
            self.ballotScanGroup)
        self.scannerInputLine = QLineEdit(self.ballotScanGroup)
        self.ballotScanPushButton = QPushButton("Add Ballot", self.ballotScanGroup)

        self.scannedBallotsGroup = QGroupBox(1, Qt.Vertical, "Scanned Ballots", self)
        self.scannedBallotTable = Table(self.scannedBallotsGroup)
        self.scannedBallotTable.setNumCols(self.scannedBallotTable.numCols() + 1)
        self.scannedBallotTable.horizontalHeader().setLabel(self.scannedBallotTable.numCols() - 1, "Ballot Filename")
        self.scannedBallotTable.setNumRows(1)
        self.scannedBallotTable.setNumCols(1)

        self.vBoxLayout.add(self.scanCountLabel)
        self.vBoxLayout.add(self.ballotScanGroup)
        self.vBoxLayout.add(self.scannedBallotsGroup)


class LoadDataPage(WizardPage):
    def __init__(self, parent, title):
        WizardPage.__init__(self, parent, title)
        self.instructionsLabel.setText("One by one, insert the data disks from the vote stations and load the ballot data. \
Be sure to load the data from all vote stations.")

        self.loadDataLabel = InfoLabel("<b>0</b> data disks to be read", self)
        self.loadDataPushButton = QPushButton("Load Vote Station Data Disk...", self)

        self.voteStationStatusGroup = QGroupBox(1, Qt.Vertical, "Vote Station Status", self)
        self.voteStationTable = Table(self.voteStationStatusGroup)
        self.voteStationTable.setNumCols(self.voteStationTable.numCols() + 3)
        self.voteStationTable.horizontalHeader().setLabel(self.voteStationTable.numCols() - 3, "Serial")
        self.voteStationTable.horizontalHeader().setLabel(self.voteStationTable.numCols() - 2, "Status")
        self.voteStationTable.horizontalHeader().setLabel(self.voteStationTable.numCols() - 1, "Ballots")
        self.voteStationTable.setNumRows(1)
        self.voteStationTable.setNumCols(3)

        self.vBoxLayout.add(self.loadDataLabel)
        self.vBoxLayout.add(self.loadDataPushButton)
        self.vBoxLayout.add(self.voteStationStatusGroup)


class RegisterBallotsPage(WizardPage):
    def __init__(self, parent, title):
        WizardPage.__init__(self, parent, title)

        self.registerBallotGroup = QGroupBox(2, Qt.Vertical, "Register A Ballot", self)
        hBox = QHBox(self.registerBallotGroup)
        hBox.setSpacing(6)
        self.registerBallotLabel = QLabel("Ballot ID", hBox)
        self.registerBallotInputLine = QLineEdit(hBox)
        self.registerBallotPushButton = QPushButton("Add Ballot ID", self.registerBallotGroup)

        self.registeredBallotsGroup = QGroupBox(1, Qt.Vertical, "Registered Ballots", self)
        self.registeredBallotsTable = Table(self.registeredBallotsGroup)
        self.registeredBallotsTable.setNumCols(self.registeredBallotsTable.numCols() + 1)
        self.registeredBallotsTable.horizontalHeader().setLabel(self.registeredBallotsTable.numCols() - 1, "Ballot ID")
        self.registeredBallotsTable.setNumRows(1)
        self.registeredBallotsTable.setNumCols(1)

        self.vBoxLayout.add(self.registerBallotGroup)
        self.vBoxLayout.add(self.registeredBallotsGroup)


class RegisterTestBallotsPage(RegisterBallotsPage):
    def __init__(self, parent, title):
        RegisterBallotsPage.__init__(self, parent, title)
        self.instructionsLabel.setText("Enter the ballot ID number for each of the test ballots that were printed on start up.")
        self.registerBallotGroup.setTitle("Register A Test Ballot")
        self.registerBallotPushButton.setText("Add Test Ballot ID")
        self.registeredBallotsGroup.setTitle("Registered Test Ballots")


class RegisterSpoiledBallotsPage(RegisterBallotsPage):
    def __init__(self, parent, title):
        RegisterBallotsPage.__init__(self, parent, title)
        self.instructionsLabel.setText("Enter the ballot ID number for all known spoiled ballots.")
        self.registerBallotGroup.setTitle("Register A Spoiled Ballot")
        self.registerBallotPushButton.setText("Add Spoiled Ballot ID")
        self.registeredBallotsGroup.setTitle("Registered Spoiled Ballots")


class CompareBallotsPage(WizardPage):
    def __init__(self, parent, title):
        WizardPage.__init__(self, parent, title)
        self.instructionsLabel.setText("You are now ready to perform the reconciliation process. \
Once done, a report will be generated and can be printed or saved to disk.")

        self.compareBallotsPushButton = QPushButton("Begin Ballot Reconciliation", self)
        hBox1 = QHBox(self)
        hBox1.setSpacing(6)
        self.compareBallotsProgressLabel = QLabel("Progress", hBox1)
        self.compareBallotsProgressBar = QProgressBar(hBox1)

        self.resultsGroup = QGroupBox(2, Qt.Vertical, "Results", self)
        self.resultsTabWidget = QTabWidget(self.resultsGroup)
        self.summaryTab = QWidget(self.resultsTabWidget)
        gridLayout1 = QGridLayout(self.summaryTab, 1, 1, 2, 0)
        self.resultStatisticsListView = QListView(self.summaryTab)
        self.resultStatisticsListView.addColumn("Count")
        self.resultStatisticsListView.addColumn("Type")
        self.processedBallotsResult = QListViewItem(self.resultStatisticsListView, str(0), "Ballots Processed")
        self.votedBallotsResult = QListViewItem(self.resultStatisticsListView, str(0), "Voted Ballots")
        self.testBallotsResult = QListViewItem(self.resultStatisticsListView, str(0), "Test Ballots")
        self.spoiledBallotsResult = QListViewItem(self.resultStatisticsListView, str(0), "Spoiled Ballots")
        self.unaccountedBallotsResult = QListViewItem(self.resultStatisticsListView, str(0), "Unaccounted Ballots")
        self.errorResult = QListViewItem(self.resultStatisticsListView, str(0), "Errors/Warnings")
        gridLayout1.addWidget(self.resultStatisticsListView, 0, 0)
        self.resultsTabWidget.insertTab(self.summaryTab, "Summary")

        self.errorsTab = QWidget(self.resultsTabWidget)
        gridLayout2 = QGridLayout(self.errorsTab, 1, 1, 2, 0)
        self.errorsTable = Table(self.errorsTab)
        self.errorsTable.setNumCols(self.errorsTable.numCols() + 2)
        self.errorsTable.horizontalHeader().setLabel(0, "Type")
        self.errorsTable.horizontalHeader().setLabel(1, "Description")
        self.errorsTable.setNumRows(1)
        self.errorsTable.setNumCols(2)
        gridLayout2.addWidget(self.errorsTable, 0, 0)
        self.resultsTabWidget.insertTab(self.errorsTab, "Errors/Warnings")


        hBox2 = QHBox(self.resultsGroup)
        hBox2.setSpacing(6)
        self.saveReportPushButton = QPushButton("Save Report...", hBox2)
        self.printReportPushButton = QPushButton("Print Report...", hBox2)

        self.vBoxLayout.add(self.compareBallotsPushButton)
        self.vBoxLayout.add(hBox1)
        self.vBoxLayout.add(self.resultsGroup)


# Special Components
# -----------------------------------------------------------------------------

class XMLBallotReader:
    pass


class XMLBallotWriter:
    pass


class ScannerInputLine(QLineEdit):
    def __init__(self, *args):
        QLineEdit.__init__(self, *args)


class BarcodeValidator(QRegExpValidator):
    def __init__(self, *args):
        QRegExpValidator.__init__(self, *args)


class InfoLabel(QLabel):
    def __init__(self, *args):
        QLabel.__init__(self, *args)
        self.setPaletteBackgroundColor(QColor(255,255,238))
        self.setFrameShape(QLabel.Box)
        self.setMargin(2)


class Table(QTable):
    def __init__(self, *args):
        QTable.__init__(self, *args)
        self.setReadOnly(True)
        self.setSelectionMode(QTable.NoSelection)

if __name__ == "__main__":
    app = QApplication(sys.argv)
    wizard = BRPWizard()
    app.setMainWidget(wizard)
    wizard.show()
    app.connect(app, SIGNAL("lastWindowClosed()"), app, SLOT("quit()"))
    app.exec_loop()