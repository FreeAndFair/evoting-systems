package software.engine.gui;
import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Calendar;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;

import javax.swing.WindowConstants;

import org.gwu.voting.standardFormat.electionSpecification.ElectionSpecification;
import org.w3c.dom.Document;

import com.sun.org.apache.xerces.internal.impl.dv.util.Base64;

import software.authoring.invisibleink.PrintableBallotMakerWithBarcodes;
import software.common.BallotGeometry;
import software.common.InputConstants;
import software.common.Util;
import software.engine.MeetingOne;
import software.engine.invisibleink.Test;
import software.engine.ioExample.MeetingOneIn;


/**
* This code was edited or generated using CloudGarden's Jigloo
* SWT/Swing GUI Builder, which is free for non-commercial
* use. If Jigloo is being used commercially (ie, by a corporation,
* company or business for any purpose whatever) then you
* should purchase a license for each developer using Jigloo.
* Please visit www.cloudgarden.com for details.
* Use of Jigloo implies acceptance of these licensing terms.
* A COMMERCIAL LICENSE HAS NOT BEEN PURCHASED FOR
* THIS MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED
* LEGALLY FOR ANY CORPORATE OR COMMERCIAL PURPOSE.
*/
public class ElectionConsole extends javax.swing.JFrame implements ElectionConsoleInterface{
	private JTabbedPane jTabbedPane;
	private JPanel jPanelFolders;
	private JPanel jPanelPublicFolder;
	private JPanel jPanelPrivateFolder;
	private JButton jButtonGo;
	private JLabel jLabelPrivateFolder;
	private JTextField jTextFieldPrivateFolder;
	private JPanel jPanelM4;
	private JTextField jTextFieldElectionConstant;
	private JLabel jLabel4;
	private JButton jButtonBallotBackground;
	private JTextField jTextFieldBallotBackground;
	private JLabel jLabelBallotBackground;
	private JTextField jTextFieldPDFFrom;
	private JLabel jLabelPDFFrom;
	private JPanel jPanel1;
	private JPanel jPanelPublishResults;
	private JPanel jPanelCheckSpoiledBallots;
	private JPanel jPanelRevealSpoiledBallots;
	private JPanel jPanelShowAllConfirmationCodes;
	private JPanel jPanelAuditConfirmationCodes;
	private JPanel jPanelGenerateRandomlyVotedBallots;
	private JCheckBox jCheckBoxPublishAllConfirmationCodesOnCastBallots;
	private JCheckBox jCheckBoxAuditAllConfirmationCodesOnCastBallots;
	private JPanel jPanelPDFSerialNumbers;
	private JPanel jPanelBallotBackground;
	private JPanel jPanelGeneratePDFs;
	private JCheckBox jCheckBoxMakePDFs;
	private JCheckBox jCheckBoxAuditM2;
	private JCheckBox jCheckBoxRunM2;
	private JCheckBox jCheckBoxGenerateRandomChallengesM2;
	private JPanel jPanelRunM2;
	private JPanel jPanelClearTextBallots;
	private JButton jButtonClearTextBallots;
	private JTextField jTextFieldClearTextBallots;
	private JLabel jLabelClearTextBallots;
	private JPanel jPanelComputeConfirmationCodes;
	private JButton jButtonGeometry;
	private JTextField jTextFieldGeometry;
	private JLabel jLabelGeometry;
	private JPanel jPanelGeometry;
	private JCheckBox jCheckBoxAuditM4;
	private JCheckBox jCheckBoxRunM4;
	private JCheckBox jCheckBoxGenerateRandomChallengesM4;
	private JPanel jPanelRunM4;
	private JCheckBox jCheckBoxPublishResults;
	private JCheckBox jCheckBoxCheckSpoiledBallots;
	private JCheckBox jCheckBoxRevealSpoiledBallots;
	private JCheckBox jCheckBoxAuditConfirmationCodes;
	private JCheckBox jCheckBoxComputeConfirmationCodes;
	private JCheckBox jCheckBoxGenerateRandomlyVotedBallots;
	private JButton jButtonPDFDestination;
	private JTextField jTextFieldPDFDestination;
	private JLabel jLabelPDFDestination;
	private JPanel jPanelPDFDestination;
	private JTextField jTextFieldPDFTo;
	private JLabel jLabelPDFTo;
	private JCheckBox jCheckBoxRunM1;
	private JPanel jPanelRunM1;
	private JPanel jPanelPartitions;
	private JPanel jPanelElectionSpec;
	private JPanel jPanelNoBallotsAndDTables;
	private JPanel jPanelPublicConstant;
	private JButton jButtonPartitions;
	private JTextField jTextFieldPartitions;
	private JLabel jLabelPartitions;
	private JButton jbES;
	private JTextField jTextFieldElectionSpec;
	private JLabel jLabelElectionSpecification;
	private JTextField jTextFieldNumberOfDTables;
	private JLabel jLabel5;
	private JTextField jTextFieldNumberOfBallots;
	private JLabel jLabel3;
	private JPanel jPanelMeetingOneConfigurationFile;
	private JPanel jPanelM3;
	private JPanel jPanelM2;
	private JPanel jPanelM1;
	private JTextArea jTextAreaLog;
	private JScrollPane jScrollPaneLog;
	private JButton jButtonPrivateFolder;
	private JButton jButtonPublicFolder;
	private JTextField jTextFieldPublicFolder;
	private JLabel jLabelPublicFolder;
	private JPanel jPanelGo;

	
	private JFileChooser jFileChooser=new JFileChooser(InputConstants.publicFolder);;
	
	boolean overwriteExistingFiles=false;
	
	/**
	* Auto-generated main method to display this JFrame
	*/
	public static void main(String[] args) {
		InputConstants.MK1=null;
		InputConstants.MK2=null;
		
		ElectionConsole inst = new ElectionConsole();
		inst.setVisible(true);
	}
	
	public ElectionConsole() {
		super();
		initGUI();
	}
	
	private void initGUI() {
		try {
			setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
			{
				jTabbedPane = new JTabbedPane();
				getContentPane().add(jTabbedPane, BorderLayout.CENTER);
				{
					jPanelM1 = new JPanel();
					BorderLayout jPanelMeetingOneLayout = new BorderLayout();
					jPanelM1.setLayout(jPanelMeetingOneLayout);
					jTabbedPane.addTab(
						"Compute Commitments",
						null,
						jPanelM1,
						null);
					{
						jPanelMeetingOneConfigurationFile = new JPanel();
						GridLayout jPanel1Layout = new GridLayout(4, 1);
						jPanel1Layout.setColumns(1);
						jPanel1Layout.setHgap(5);
						jPanel1Layout.setVgap(5);
						jPanel1Layout.setRows(4);
						jPanelMeetingOneConfigurationFile.setLayout(jPanel1Layout);
						//jPanelM1.add(jPanelMeetingOneConfigurationFile, BorderLayout.CENTER);
						{
							jPanelPublicConstant = new JPanel();
							jPanelMeetingOneConfigurationFile.add(jPanelPublicConstant);
							{
								jLabel3 = new JLabel();
								jPanelPublicConstant.add(jLabel3);
								jLabel3.setText("Public Constant");
							}
							{
								jTextFieldElectionConstant = new JTextField();
								jPanelPublicConstant.add(jTextFieldElectionConstant);
								jTextFieldElectionConstant.setPreferredSize(new java.awt.Dimension(
									262,
									20));
							}
						}
						{
							jPanelNoBallotsAndDTables = new JPanel();
							jPanelMeetingOneConfigurationFile.add(jPanelNoBallotsAndDTables);
							{
								jLabel4 = new JLabel();
								jPanelNoBallotsAndDTables.add(jLabel4);
								jLabel4.setText("Number Of Ballots");
							}
							{
								jTextFieldNumberOfBallots = new JTextField();
								jPanelNoBallotsAndDTables.add(jTextFieldNumberOfBallots);
								jTextFieldNumberOfBallots.setPreferredSize(new java.awt.Dimension(
									60,
									20));
							}
							{
								jLabel5 = new JLabel();
								jPanelNoBallotsAndDTables.add(jLabel5);
								jLabel5.setText("Number Of D Tables");
							}
							{
								jTextFieldNumberOfDTables = new JTextField();
								jPanelNoBallotsAndDTables.add(jTextFieldNumberOfDTables);
								jTextFieldNumberOfDTables
									.setPreferredSize(new java.awt.Dimension(
										60,
										20));
							}
						}
						{
							jPanelElectionSpec = new JPanel();
							jPanelMeetingOneConfigurationFile.add(jPanelElectionSpec);
							{
								jLabelElectionSpecification = new JLabel();
								jPanelElectionSpec
									.add(jLabelElectionSpecification);
								jLabelElectionSpecification
									.setText("ElectionSpec");
								jLabelElectionSpecification
									.setPreferredSize(new java.awt.Dimension(
										79,
										14));
							}
							{
								jTextFieldElectionSpec = new JTextField();
								jPanelElectionSpec.add(jTextFieldElectionSpec);
								jTextFieldElectionSpec.setEditable(true);
								jTextFieldElectionSpec
									.setPreferredSize(new java.awt.Dimension(
										207,
										20));
							}
							{
								jbES = new JButton();
								jPanelElectionSpec.add(jbES);
								jbES.setText("Browse");
								jbES.addActionListener(new ActionListener() {
									public void actionPerformed(ActionEvent evt) {
										selectFolder(
											JFileChooser.FILES_ONLY,
											"Select the Election Specification file",
											InputConstants.ElectionSpec,
											jTextFieldElectionSpec);
									}
								});
							}
						}
						{
							jPanelPartitions = new JPanel();
							jPanelMeetingOneConfigurationFile.add(jPanelPartitions);
							{
								jLabelPartitions = new JLabel();
								jPanelPartitions.add(jLabelPartitions);
								jLabelPartitions.setText("Partitions");
								jLabelPartitions
									.setPreferredSize(new java.awt.Dimension(
										79,
										14));
							}
							{
								jTextFieldPartitions = new JTextField();
								jPanelPartitions.add(jTextFieldPartitions);
								jTextFieldPartitions
									.setPreferredSize(new java.awt.Dimension(
										207,
										20));
							}
							{
								jButtonPartitions = new JButton();
								jPanelPartitions.add(jButtonPartitions);
								jButtonPartitions.setText("Browse");
								jButtonPartitions
									.addActionListener(new ActionListener() {
										public void actionPerformed(
											ActionEvent evt) {
											selectFolder(
												JFileChooser.FILES_ONLY,
												"Select the Partitions file",
												InputConstants.Partitions,
												jTextFieldPartitions);
										}
									});
							}
						}
					}
					{
						jPanelRunM1 = new JPanel();
						FlowLayout jPanelRunM1Layout = new FlowLayout();
						jPanelRunM1Layout.setAlignment(FlowLayout.LEFT);
						jPanelRunM1.setLayout(jPanelRunM1Layout);
						jPanelM1.add(
							jPanelRunM1,
							BorderLayout.NORTH);
						{
							jCheckBoxRunM1 = new JCheckBox();
							jPanelRunM1.add(jCheckBoxRunM1);
							jCheckBoxRunM1
								.setText("Commit to how the ballots are going to be decrypted");
						}
					}
				}
				{
					jPanelM2 = new JPanel();
					BorderLayout jPanelMeetingTwoLayout = new BorderLayout();
					jPanelM2.setLayout(jPanelMeetingTwoLayout);
					jTabbedPane.addTab(
						"Check Commitments",
						null,
						jPanelM2,
						null);
					{
						jPanelRunM2 = new JPanel();
						jPanelM2.add(jPanelRunM2, BorderLayout.NORTH);
						GridLayout jPanelRunM2Layout = new GridLayout(3, 1);
						jPanelRunM2Layout.setColumns(1);
						jPanelRunM2Layout.setHgap(5);
						jPanelRunM2Layout.setVgap(5);
						jPanelRunM2Layout.setRows(3);
						jPanelRunM2.setLayout(jPanelRunM2Layout);
						{
							jCheckBoxGenerateRandomChallengesM2 = new JCheckBox();
							jPanelRunM2
								.add(jCheckBoxGenerateRandomChallengesM2);
							jCheckBoxGenerateRandomChallengesM2
								.setText("Generate random challenges");
							jCheckBoxGenerateRandomChallengesM2.setForeground(new java.awt.Color(128,128,128));
						}
						{
							jCheckBoxRunM2 = new JCheckBox();
							jPanelRunM2.add(jCheckBoxRunM2);
							jCheckBoxRunM2
								.setText("Show how the challenges ballots are decrypted");
						}
						{
							jCheckBoxAuditM2 = new JCheckBox();
							jPanelRunM2.add(jCheckBoxAuditM2);
							jCheckBoxAuditM2
								.setText("Check that the challenged ballots are correctly formed");
						}
					}
					{
						jPanelGeneratePDFs = new JPanel();
						jPanelM2.add(jPanelGeneratePDFs, BorderLayout.SOUTH);
						GridLayout jPanelGeneratePDFsLayout = new GridLayout(
							5,
							1);
						jPanelGeneratePDFsLayout.setColumns(1);
						jPanelGeneratePDFsLayout.setHgap(5);
						jPanelGeneratePDFsLayout.setRows(5);
						jPanelGeneratePDFsLayout.setVgap(2);
						jPanelGeneratePDFs.setLayout(jPanelGeneratePDFsLayout);
						{
							jCheckBoxMakePDFs = new JCheckBox();
							jPanelGeneratePDFs.add(jCheckBoxMakePDFs);
							jCheckBoxMakePDFs
								.setText("Generate PDF ballots for printing");
						}
						{
							jPanelGeometry = new JPanel();
							FlowLayout jPanelGeometryLayout = new FlowLayout();
							jPanelGeometryLayout.setVgap(1);
							jPanelGeometry.setLayout(jPanelGeometryLayout);
							//jPanelGeneratePDFs.add(jPanelGeometry);
							{
								jLabelGeometry = new JLabel();
								jPanelGeometry.add(jLabelGeometry);
								jLabelGeometry.setText("Ballot Geometry");
								jLabelGeometry.setPreferredSize(new java.awt.Dimension(110, 14));
							}
							{
								jTextFieldGeometry = new JTextField();
								jPanelGeometry.add(jTextFieldGeometry);
								jTextFieldGeometry
									.setPreferredSize(new java.awt.Dimension(
										207,
										20));
							}
							{
								jButtonGeometry = new JButton();
								jPanelGeometry.add(jButtonGeometry);
								jButtonGeometry.setText("Browse");
								jButtonGeometry
									.addActionListener(new ActionListener() {
									public void actionPerformed(ActionEvent evt) {
										selectFolder(
											JFileChooser.FILES_ONLY,
											"Where the should the voter mark ?",
											InputConstants.Geometry,
											jTextFieldGeometry);
									}
									});
							}
						}
						{
							jPanelBallotBackground = new JPanel();
							FlowLayout jPanelBallotBackgroundLayout = new FlowLayout();
							jPanelBallotBackgroundLayout.setVgap(1);
							jPanelBallotBackground.setLayout(jPanelBallotBackgroundLayout);
							//jPanelGeneratePDFs.add(jPanelBallotBackground);
							{
								jLabelBallotBackground = new JLabel();
								jPanelBallotBackground.add(jLabelBallotBackground);
								jLabelBallotBackground.setText("Ballot Template");
								jLabelBallotBackground.setPreferredSize(new java.awt.Dimension(110, 14));
							}
							{
								jTextFieldBallotBackground = new JTextField();
								jPanelBallotBackground.add(jTextFieldBallotBackground);
								jTextFieldBallotBackground
									.setPreferredSize(new java.awt.Dimension(
										207,
										20));
							}
							{
								jButtonBallotBackground = new JButton();
								jPanelBallotBackground.add(jButtonBallotBackground);
								jButtonBallotBackground.setText("Browse");
								jButtonBallotBackground
									.addActionListener(new ActionListener() {
									public void actionPerformed(ActionEvent evt) {
										selectFolder(
												JFileChooser.FILES_ONLY,
												"PDF to use for the ballot template", 
												InputConstants.PdfTemplate, 
												jTextFieldBallotBackground);
									}
									});
							}
						}
						{
							jPanelPDFSerialNumbers = new JPanel();
							FlowLayout jPanelPDFSerialNumbersLayout = new FlowLayout();
							jPanelPDFSerialNumbersLayout.setVgap(1);
							jPanelPDFSerialNumbers.setLayout(jPanelPDFSerialNumbersLayout);
							jPanelGeneratePDFs.add(jPanelPDFSerialNumbers);
							{
								jLabelPDFFrom = new JLabel();
								jPanelPDFSerialNumbers.add(jLabelPDFFrom);
								jLabelPDFFrom.setText("From Serial No");
							}
							{
								jTextFieldPDFFrom = new JTextField();
								jPanelPDFSerialNumbers.add(jTextFieldPDFFrom);
								jTextFieldPDFFrom.setText("0");
								jTextFieldPDFFrom
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
							{
								jLabelPDFTo = new JLabel();
								jPanelPDFSerialNumbers.add(jLabelPDFTo);
								jLabelPDFTo.setText("To Serial No");
							}
							{
								jTextFieldPDFTo = new JTextField();
								jPanelPDFSerialNumbers.add(jTextFieldPDFTo);
								jTextFieldPDFTo.setText("1000");
								jTextFieldPDFTo
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
						}
						{
							jPanelPDFDestination = new JPanel();
							FlowLayout jPanelPDFDestinationLayout = new FlowLayout();
							jPanelPDFDestinationLayout.setVgap(1);
							jPanelPDFDestination.setLayout(jPanelPDFDestinationLayout);
							//jPanelGeneratePDFs.add(jPanelPDFDestination);
							{
								jLabelPDFDestination = new JLabel();
								jPanelPDFDestination.add(jLabelPDFDestination);
								jLabelPDFDestination
									.setText("Destination Folder");
								jLabelPDFDestination.setPreferredSize(new java.awt.Dimension(110, 14));
							}
							{
								jTextFieldPDFDestination = new JTextField();
								jPanelPDFDestination.add(jTextFieldPDFDestination);
								jTextFieldPDFDestination.setPreferredSize(new java.awt.Dimension(207, 20));
							}
							{
								jButtonPDFDestination = new JButton();
								jPanelPDFDestination.add(jButtonPDFDestination);
								jButtonPDFDestination.setText("Browse");
								jButtonPDFDestination
									.addActionListener(new ActionListener() {
									public void actionPerformed(ActionEvent evt) {
										selectFolder(JFileChooser.DIRECTORIES_ONLY,"Where to put the PDF ballots", InputConstants.privateFolder, jTextFieldPDFDestination);
									}
									});
							}
						}
					}
				}
				{
					jPanelM3 = new JPanel();
					GridLayout jPanelMeetingThreeLayout = new GridLayout(6, 1);
					jPanelMeetingThreeLayout.setColumns(1);
					jPanelMeetingThreeLayout.setHgap(5);
					jPanelMeetingThreeLayout.setVgap(5);
					jPanelMeetingThreeLayout.setRows(6);
					jPanelM3.setLayout(jPanelMeetingThreeLayout);
					jTabbedPane.addTab(
						"Compute Results",
						null,
						jPanelM3,
						null);
					{
						jPanelGenerateRandomlyVotedBallots = new JPanel();
						GridLayout jPanelGenerateRandomlyVotedBallotsLayout = new GridLayout(
							1,
							1);
						jPanelGenerateRandomlyVotedBallotsLayout.setHgap(5);
						jPanelGenerateRandomlyVotedBallotsLayout.setVgap(5);
						jPanelGenerateRandomlyVotedBallotsLayout.setColumns(1);
						jPanelGenerateRandomlyVotedBallots.setLayout(jPanelGenerateRandomlyVotedBallotsLayout);
						jPanelM3.add(jPanelGenerateRandomlyVotedBallots);
						{
							jCheckBoxGenerateRandomlyVotedBallots = new JCheckBox();
							jPanelGenerateRandomlyVotedBallots.add(jCheckBoxGenerateRandomlyVotedBallots);
							jCheckBoxGenerateRandomlyVotedBallots
								.setText("Generate Randomly Voted Ballots");
							jCheckBoxGenerateRandomlyVotedBallots
								.setForeground(new java.awt.Color(128, 128, 128));
						}
					}
					{
						jPanelComputeConfirmationCodes = new JPanel();
						GridLayout jPanelComputeConfirmationCodesLayout = new GridLayout(
							1,
							2);
						jPanelComputeConfirmationCodesLayout.setHgap(5);
						jPanelComputeConfirmationCodesLayout.setVgap(5);
						jPanelComputeConfirmationCodesLayout.setColumns(2);
						jPanelComputeConfirmationCodes.setLayout(jPanelComputeConfirmationCodesLayout);
						jPanelM3.add(jPanelComputeConfirmationCodes);
						{
							jPanel1 = new JPanel();
							FlowLayout jPanel1Layout = new FlowLayout();
							jPanel1Layout.setAlignment(FlowLayout.LEFT);
							jPanel1Layout.setHgap(0);
							jPanel1.setLayout(jPanel1Layout);
							jPanelComputeConfirmationCodes.add(jPanel1);
							{
								jCheckBoxComputeConfirmationCodes = new JCheckBox();
								jPanel1.add(jCheckBoxComputeConfirmationCodes);
								jCheckBoxComputeConfirmationCodes
									.setText("Compute the Confirmation Codes that the Voters Got");
							}
						}
						{
							jPanelClearTextBallots = new JPanel();
							FlowLayout jPanelClearTextBallotsLayout = new FlowLayout();
							jPanelClearTextBallotsLayout.setAlignment(FlowLayout.LEFT);
							jPanelClearTextBallots.setLayout(jPanelClearTextBallotsLayout);
							//jPanelComputeConfirmationCodes.add(jPanelClearTextBallots);
							{
								jLabelClearTextBallots = new JLabel();
								jPanelClearTextBallots.add(jLabelClearTextBallots);
								jLabelClearTextBallots.setText("Ballots");
							}
							{
								jTextFieldClearTextBallots = new JTextField();
								jPanelClearTextBallots.add(jTextFieldClearTextBallots);
								jTextFieldClearTextBallots
									.setPreferredSize(new java.awt.Dimension(
										207,
										20));
							}
							{
								jButtonClearTextBallots = new JButton();
								jPanelClearTextBallots.add(jButtonClearTextBallots);
								jButtonClearTextBallots.setText("Browse");
								jButtonClearTextBallots
									.addActionListener(new ActionListener() {
										public void actionPerformed(
											ActionEvent evt) {
											selectFolder(
												JFileChooser.FILES_AND_DIRECTORIES,
												"The folder/file with the scannes ballots",
												InputConstants.BallotsDir,
												jTextFieldClearTextBallots);
										}
									});
							}
						}
					}
					{
						jPanelAuditConfirmationCodes = new JPanel();
						GridLayout jPanelAuditConfirmationCodesLayout = new GridLayout(
							1,
							1);
						jPanelAuditConfirmationCodesLayout.setHgap(5);
						jPanelAuditConfirmationCodesLayout.setVgap(5);
						jPanelAuditConfirmationCodesLayout.setColumns(1);
						jPanelAuditConfirmationCodes.setLayout(jPanelAuditConfirmationCodesLayout);
						jPanelM3.add(jPanelAuditConfirmationCodes);
						{
							jCheckBoxAuditConfirmationCodes = new JCheckBox();
							jPanelAuditConfirmationCodes.add(jCheckBoxAuditConfirmationCodes);
							jCheckBoxAuditConfirmationCodes
								.setText("Audit the Confirmation Codes (verify their commitments)");
						}
					}
					{
						jPanelRevealSpoiledBallots = new JPanel();
						GridLayout jPanelRevealSpoiledBallotsLayout = new GridLayout(
							1,
							1);
						jPanelRevealSpoiledBallotsLayout.setHgap(5);
						jPanelRevealSpoiledBallotsLayout.setVgap(5);
						jPanelRevealSpoiledBallotsLayout.setColumns(1);
						jPanelRevealSpoiledBallots.setLayout(jPanelRevealSpoiledBallotsLayout);
						jPanelM3.add(jPanelRevealSpoiledBallots);
						{
							jCheckBoxRevealSpoiledBallots = new JCheckBox();
							jPanelRevealSpoiledBallots.add(jCheckBoxRevealSpoiledBallots);
							jCheckBoxRevealSpoiledBallots
								.setText("Print audit all the ballots except the voted ones and the spoiled ones");
						}
					}
					{
						jPanelCheckSpoiledBallots = new JPanel();
						GridLayout jPanelCheckSpoiledBallotsLayout = new GridLayout(
							1,
							1);
						jPanelCheckSpoiledBallotsLayout.setHgap(5);
						jPanelCheckSpoiledBallotsLayout.setVgap(5);
						jPanelCheckSpoiledBallotsLayout.setColumns(1);
						jPanelCheckSpoiledBallots.setLayout(jPanelCheckSpoiledBallotsLayout);
						jPanelM3.add(jPanelCheckSpoiledBallots);
						{
							jCheckBoxCheckSpoiledBallots = new JCheckBox();
							jPanelCheckSpoiledBallots.add(jCheckBoxCheckSpoiledBallots);
							jCheckBoxCheckSpoiledBallots
								.setText("Check All the Opened Spoiled Ballots ");
						}
					}
					{
						jPanelPublishResults = new JPanel();
						GridLayout jPanelPublishResultsLayout = new GridLayout(
							1,
							1);
						jPanelPublishResultsLayout.setHgap(5);
						jPanelPublishResultsLayout.setVgap(5);
						jPanelPublishResultsLayout.setColumns(1);
						jPanelPublishResults.setLayout(jPanelPublishResultsLayout);
						jPanelM3.add(jPanelPublishResults);
						{
							jCheckBoxPublishResults = new JCheckBox();
							jPanelPublishResults.add(jCheckBoxPublishResults);
							jCheckBoxPublishResults.setText("Publish Results");
						}
					}
				}
				{
					jPanelM4 = new JPanel();
					jTabbedPane.addTab("Check Results", null, jPanelM4, null);
					BorderLayout jPanelM4Layout = new BorderLayout();
					jPanelM4.setLayout(jPanelM4Layout);
					{
						jPanelRunM4 = new JPanel();
						jPanelM4.add(jPanelRunM4, BorderLayout.NORTH);
						GridLayout jPanel1Layout1 = new GridLayout(3, 1);
						jPanel1Layout1.setColumns(1);
						jPanel1Layout1.setRows(3);
						jPanel1Layout1.setHgap(5);
						jPanel1Layout1.setVgap(5);
						jPanelRunM4.setLayout(jPanel1Layout1);
						{
							jCheckBoxGenerateRandomChallengesM4 = new JCheckBox();
							jPanelRunM4.add(jCheckBoxGenerateRandomChallengesM4);
							jCheckBoxGenerateRandomChallengesM4.setText("Generate random challenges");
							jCheckBoxGenerateRandomChallengesM4.setForeground(new java.awt.Color(128,128,128));
						}
						{
							jCheckBoxRunM4 = new JCheckBox();
							jPanelRunM4.add(jCheckBoxRunM4);
							jCheckBoxRunM4.setText("Show how the challenged ballots are decrypted");
						}
						{
							jCheckBoxAuditM4 = new JCheckBox();
							jPanelRunM4.add(jCheckBoxAuditM4);
							jCheckBoxAuditM4
								.setText("Check that the challenged ballots are correctly formed");
						}
					}
					{
						jPanelShowAllConfirmationCodes = new JPanel();
						GridLayout jPanelShowAllConfirmationCodesLayout = new GridLayout(
							2,
							1);
						jPanelShowAllConfirmationCodesLayout.setHgap(5);
						jPanelShowAllConfirmationCodesLayout.setVgap(5);
						jPanelShowAllConfirmationCodesLayout.setColumns(1);
						jPanelShowAllConfirmationCodesLayout.setRows(2);
						jPanelShowAllConfirmationCodes.setLayout(jPanelShowAllConfirmationCodesLayout);
						jPanelM4.add(
							jPanelShowAllConfirmationCodes,
							BorderLayout.SOUTH);
						{
							jCheckBoxPublishAllConfirmationCodesOnCastBallots = new JCheckBox();
							jPanelShowAllConfirmationCodes.add(jCheckBoxPublishAllConfirmationCodesOnCastBallots);
							jCheckBoxPublishAllConfirmationCodesOnCastBallots
								.setText("Publish All Confirmation Codes on All Cast Ballots");
						}
						{
							jCheckBoxAuditAllConfirmationCodesOnCastBallots = new JCheckBox();
							jPanelShowAllConfirmationCodes.add(jCheckBoxAuditAllConfirmationCodesOnCastBallots);
							jCheckBoxAuditAllConfirmationCodesOnCastBallots
								.setText("Audit the Confirmation Codes on All Cast Ballots");
						}
					}
				}
			}
			{
				jPanelFolders = new JPanel();
				GridLayout jPanelFoldersLayout = new GridLayout(3, 1);
				jPanelFoldersLayout.setColumns(1);
				jPanelFoldersLayout.setHgap(5);
				jPanelFoldersLayout.setVgap(5);
				jPanelFoldersLayout.setRows(3);
				jPanelFolders.setLayout(jPanelFoldersLayout);
				getContentPane().add(jPanelFolders, BorderLayout.NORTH);
				{
					jPanelPublicFolder = new JPanel();
					jPanelFolders.add(jPanelPublicFolder);
					{
						jLabelPublicFolder = new JLabel();
						jPanelPublicFolder.add(jLabelPublicFolder);
						jLabelPublicFolder.setText("Public Folder");
						jLabelPublicFolder.setPreferredSize(new java.awt.Dimension(80, 14));
					}
					{
						jTextFieldPublicFolder = new JTextField();
						jPanelPublicFolder.add(jTextFieldPublicFolder);
						jTextFieldPublicFolder.setPreferredSize(new java.awt.Dimension(207, 20));
					}
					{
						jButtonPublicFolder = new JButton();
						jPanelPublicFolder.add(jButtonPublicFolder);
						jButtonPublicFolder.setText("Browse");
						jButtonPublicFolder
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								selectFolder(JFileChooser.DIRECTORIES_ONLY,"Election Data Public Storage Location", InputConstants.publicFolder, jTextFieldPublicFolder);
								
								autoDetect();
							}
							});
					}
				}
				{
					jPanelPrivateFolder = new JPanel();
					jPanelFolders.add(jPanelPrivateFolder);
					{
						jLabelPrivateFolder = new JLabel();
						jPanelPrivateFolder.add(jLabelPrivateFolder);
						jLabelPrivateFolder.setText("Private Folder");
						jLabelPrivateFolder.setPreferredSize(new java.awt.Dimension(80, 14));
					}
					{
						jTextFieldPrivateFolder = new JTextField();
						jPanelPrivateFolder.add(jTextFieldPrivateFolder);
						jTextFieldPrivateFolder.setPreferredSize(new java.awt.Dimension(207, 20));
					}
					{
						jButtonPrivateFolder = new JButton();
						jPanelPrivateFolder.add(jButtonPrivateFolder);
						jButtonPrivateFolder.setText("Browse");
						jButtonPrivateFolder
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								selectFolder(JFileChooser.DIRECTORIES_ONLY,"Election Data Private Storage Location", InputConstants.privateFolder, jTextFieldPrivateFolder);
								autoDetect();
								}
							});
					}
				}
				{
					jPanelGo = new JPanel();
					jPanelFolders.add(jPanelGo);
					{
						jButtonGo = new JButton();
						jPanelGo.add(jButtonGo);
						jButtonGo.setText("Go");
						jButtonGo.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								go();
							}
						});
					}
				}
			}
			{
				{
					jTextAreaLog = new JTextArea();
					jTextAreaLog.setColumns(20);
					jTextAreaLog.setEditable(false);
					jTextAreaLog.setRows(5);
				}
				jScrollPaneLog = new JScrollPane(jTextAreaLog);
				getContentPane().add(jScrollPaneLog, BorderLayout.SOUTH);
			}
			setTitle("Election Management Console");
			this.addWindowListener(new WindowAdapter() {
				public void windowClosing(WindowEvent evt) {
					WriteLog("Election Console Close Normally");
				}
			});
			pack();
			setSize(800, 600);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	void selectFolder(int mode,String title, String defaultSelection, JTextField textFiledToSet) {
        jFileChooser.setDialogTitle(title);
        
        jFileChooser.setFileSelectionMode(mode);

        jFileChooser.setCurrentDirectory(new File(defaultSelection));
        jFileChooser.setSelectedFile(new File(defaultSelection));
        jFileChooser.setVisible(true);
        int retVal = jFileChooser.showOpenDialog(this);
        
        if (retVal == JFileChooser.APPROVE_OPTION)
        {
           try {
        	   textFiledToSet.setText(jFileChooser.getSelectedFile().getCanonicalPath()+Util.fileSeparator);
           } catch (IOException e) {
        	   e.printStackTrace();
           }
        }
	}
	
	void go() {
    	StringBuffer sf=new StringBuffer();
    	sf.append("Executing: ");
    	for (JCheckBox jCheckBox:getAllCheckBoxes()) {
    		sf.append(jCheckBox.getText()+"\n");
    	}
    	WriteLog(sf.toString() + "\n");
		
        try {
        	runMeetings();
        } catch (java.security.InvalidKeyException e) {
        	sf=new StringBuffer();
        	for (StackTraceElement s:e.getStackTrace()) {
        		sf.append(s+"\n");
        	}
            WriteLog("Error: "+e+" thrown by \n"+sf.toString() + "\n");
            JOptionPane.showMessageDialog(this, "Error:"+e+"\n You do not have the Java Unrestricted Policy files (JCE) installed", "Error", JOptionPane.ERROR_MESSAGE);
            return;
        } catch (java.lang.OutOfMemoryError outofMemEx) {
        	sf=new StringBuffer();
        	for (StackTraceElement s:outofMemEx.getStackTrace()) {
        		sf.append(s+"\n");
        	}
            WriteLog("Error: "+outofMemEx+" thrown by \n"+sf.toString() + "\n");
            JOptionPane.showMessageDialog(this, "Error:"+outofMemEx+"\nOut of memory.\nIncrease the availabel memory using -Xmx512m", "Error", JOptionPane.ERROR_MESSAGE);
            return;        	
        } catch (Exception ex) {
        	sf=new StringBuffer();
        	for (StackTraceElement s:ex.getStackTrace()) {
        		sf.append(s+"\n");
        	}
            WriteLog("Error: "+ex+" thrown by \n"+sf.toString() + "\n");
            JOptionPane.showMessageDialog(this, "Error:"+ex, "Error", JOptionPane.ERROR_MESSAGE);
            return;
        }
        WriteLog("All done \n");
        JOptionPane.showMessageDialog(this, "Done", "Done", JOptionPane.INFORMATION_MESSAGE);
	}
	
    public void WriteLog(String output)
    {
    	try {
	        BufferedWriter auditLog = new BufferedWriter(new FileWriter(InputConstants.publicFolder + "/election.log", true));
	        
	        auditLog.write( "\n\n>>>>> Audit Log written " + Calendar.getInstance().getTime().toString() + " <<<<<\n" );
	        auditLog.write(output);
	        auditLog.close();
    	} catch (Exception e) {
            JOptionPane.showMessageDialog(this, "Error", "Error Writing in the log file "+InputConstants.publicFolder + "/election.log", JOptionPane.ERROR_MESSAGE);    		
    	}
    	
        if ( jTextAreaLog != null )
        	jTextAreaLog.insert( output, jTextAreaLog.getText().length() );
        System.out.println( output );
    }

    public void processKeys(int meeting) {
    	
    }
    
    void runMeetings() throws Exception {
    	overwriteExistingFiles=false;
    	
    	try {
    		checkForM1In();
    	} catch (Exception e) {
    		saveM1In();
    	}
    	
    	Test test=new Test();
    	if (jCheckBoxRunM1.isSelected() && permissionToWrite(InputConstants.MeetingOneOut) && isLogedIn()) {
    			test.testMeetingOne();
    	}
    	
    	if (jCheckBoxGenerateRandomChallengesM2.isSelected() && permissionToWrite(InputConstants.MeetingTwoIn)) {
    			test.testCreatetMeetingTwoInput();
    	}
    		
    	if (jCheckBoxRunM2.isSelected() && permissionToWrite(InputConstants.MeetingTwoOut)&& isLogedIn()) {
    			test.testMeetingTwo();
    	}
    	
    	if (jCheckBoxAuditM2.isSelected())
    		test.testPreElectionAudit();
    	
    	if (jCheckBoxMakePDFs.isSelected()) {
    		checkForM1In();
    		MeetingOne m1=new MeetingOne(InputConstants.MeetingOneIn);
    		
    		ElectionSpecification es=m1.getEs();
    			//new ElectionSpecification(jTextFieldElectionSpec.getText());
    		BallotGeometry geom=new BallotGeometry(jTextFieldGeometry.getText());

        	PrintableBallotMakerWithBarcodes pbm=new PrintableBallotMakerWithBarcodes(es,geom);
        	pbm.init(jTextFieldBallotBackground.getText(),InputConstants.MeetingTwoPrints);

        	//make ballots in batches
        	for (int i=Integer.parseInt(jTextFieldPDFFrom.getText());i<=Integer.parseInt(jTextFieldPDFTo.getText());i+=InputConstants.PrintBatchSize) {
        		pbm.makePrintableBallots(jTextFieldPDFDestination.getText(), i,Math.min(i+InputConstants.PrintBatchSize-1, Integer.parseInt(jTextFieldPDFTo.getText())));	
        	}
    	}
    	
    	if (jCheckBoxGenerateRandomlyVotedBallots.isSelected() && permissionToWrite(InputConstants.BallotsDir) && isLogedIn()) {
    			test.testCreateRandomVotedBallots();
    	}
    	
    	if (jCheckBoxComputeConfirmationCodes.isSelected()) {
    		InputConstants.BallotsDir=jTextFieldClearTextBallots.getText();
    		if (permissionToWrite(InputConstants.MeetingThreeOutCodes) && isLogedIn()) {
    			test.revealMarkedSymbols();
    		}
    	}
    	
    	if (jCheckBoxAuditConfirmationCodes.isSelected())
    		test.testAuditCodesForVotedCandidates();
    	
    	if (jCheckBoxRevealSpoiledBallots.isSelected() && permissionToWrite(InputConstants.PrintAuditCodes) && isLogedIn()) {
    			test.testRevealAuditedBallots();
    	}
    	
    	if (jCheckBoxCheckSpoiledBallots.isSelected()) {
    		test.testCheckAuditedBallots();
    	}
    	    	    	
    	if (jCheckBoxPublishResults.isSelected() && permissionToWrite(InputConstants.MeetingThreeOut) && isLogedIn()) {
    			test.computeResults();
    	}
    		
    	if (jCheckBoxGenerateRandomChallengesM4.isSelected() && permissionToWrite(InputConstants.MeetingFourIn)) {
    			test.testCreateMeetingFourInput();
    	}
    	
    	if (jCheckBoxRunM4.isSelected() && permissionToWrite(InputConstants.MeetingFourOut) && isLogedIn()) {
    			test.testMeetingFour();
    	}
    	
    	if (jCheckBoxAuditM4.isSelected())
    		test.testPostElectionAudit();
    	
    	if (jCheckBoxPublishAllConfirmationCodesOnCastBallots.isSelected() && permissionToWrite(InputConstants.ContestedCodes) && isLogedIn()) {
    			test.testChallengedCodes();
    	}
    		
    	if (jCheckBoxAuditAllConfirmationCodesOnCastBallots.isSelected()) {
    		test.testCodesCommitmentsAllCodesOnCastBallots();
    	}

    	setAllCheckBoxes(false);
    	autoDetect();
    }
    
    void checkForM1In() throws Exception {
		try {
			loadM1In();
		} catch (Exception e) {
			jPanelM1.requestFocus();
			throw e;
		}
		//saveM1In();
    }
    	
	/**
	 * Loads a preset MeetingOneIn XMLs 
	 * @throws Exception
	 */
	private void loadM1In() throws Exception {
		System.out.println("loading "+InputConstants.MeetingOneIn);
		
		Document doc = Util.DomParse(InputConstants.MeetingOneIn);
		jTextFieldElectionSpec.setText(doc.getElementsByTagName("electionSpec").item(0).getFirstChild().getNodeValue());
		jTextFieldNumberOfBallots.setText(doc.getElementsByTagName("noBallots").item(0).getFirstChild().getNodeValue());
		jTextFieldNumberOfDTables.setText(doc.getElementsByTagName("noDs").item(0).getFirstChild().getNodeValue());
		jTextFieldElectionConstant.setText(new String(Base64.decode(doc.getElementsByTagName("constant").item(0).getFirstChild().getNodeValue())));
		jTextFieldPartitions.setText(doc.getElementsByTagName("partitions").item(0).getFirstChild().getNodeValue());
		
		System.out.println("Done");
	}
	
	
	private void saveM1In() throws Exception {
		String c = jTextFieldElectionConstant.getText().trim();
		if (c.length() < 16) {
			while (c.length()<16)
				c=c+" ";
			//throw new Exception("The public constant has to have 16 chars. Is has "+c.length());								
		}
		if (c.length() > 16) {
			c=c.substring(0,16);
		}
		
		int noB=-1;
		
		try {
			noB = Integer.parseInt(jTextFieldNumberOfBallots.getText());
			if (noB < 1 )
				throw new Exception("");
		} catch(Exception e) {
			throw new Exception("Numbe of ballots must be an integer between > 0");																
		}
		int noDs=1;
		try {
			noDs = Integer.parseInt(jTextFieldNumberOfDTables.getText());
			if (noDs < 1 || noDs >100)
				throw new Exception("");
		} catch(Exception e) {
			throw new Exception("Numbe of D tables must be an integer between 1 and 100");																
		}
		String es=null;
		try {
			new ElectionSpecification(jTextFieldElectionSpec.getText());
			es=jTextFieldElectionSpec.getText();
		} catch (Exception e) {
			throw new Exception("Invalid ElectionSpecification file ");																			
		}
		
    	try {
    		MeetingOneIn.write(es,noB,noDs,c.getBytes(), jTextFieldPartitions.getText(), InputConstants.MeetingOneIn);
		} catch (Exception e) {
			JOptionPane.showMessageDialog(null, "Error saving "+InputConstants.MeetingOneIn, "alert", JOptionPane.ERROR_MESSAGE);				
			e.printStackTrace();
		}
	}
	
	void autoDetect() {
		InputConstants.setPublicFolder(jTextFieldPublicFolder.getText()+Util.fileSeparator);

		//jTextFieldPrivateFolder.setText(new File(InputConstants.publicFolder).getParent()+Util.fileSeparator+"private"+Util.fileSeparator);
		InputConstants.setPrivateFolder(jTextFieldPrivateFolder.getText());
		
		try {
			checkForM1In();
		} catch (Exception e) {
			//e.printStackTrace();
			
			//m1in does not exist. Help create it
			jTextFieldElectionSpec.setText(InputConstants.ElectionSpec);
			jTextFieldPartitions.setText(InputConstants.Partitions);
			jTextFieldNumberOfBallots.setText(100+"");
			jTextFieldNumberOfDTables.setText(1+"");
			jTextFieldElectionConstant.setText("Name Of Election");
			jCheckBoxRunM1.setSelected(true);
			
			return;
		}
		
		//set the default value for the text fields
		jTextFieldGeometry.setText(InputConstants.Geometry);
		jTextFieldBallotBackground.setText(InputConstants.PdfTemplate);
		jTextFieldPDFDestination.setText(InputConstants.privateFolder);
		jTextFieldClearTextBallots.setText(InputConstants.BallotsDir);
		
		//start looking for standard files to determine which stage the election is in
		if ( ! new File(InputConstants.MeetingOneOut).exists()) {
			setDefaultNextStep(jCheckBoxRunM1);
			return;
		}

		if ( ! new File(InputConstants.MeetingTwoIn).exists()) {
			setDefaultNextStep(jCheckBoxGenerateRandomChallengesM2);
			return;
		}
		
		if ( ! new File(InputConstants.MeetingTwoOut).exists()) {
			setDefaultNextStep(jCheckBoxRunM2);
			setDefaultNextStep(jCheckBoxAuditM2);
			return;
		}

		if ( ! new File(InputConstants.MeetingThreeIn).exists()) {
			setDefaultNextStep(jCheckBoxGenerateRandomlyVotedBallots);
			setDefaultNextStep(jCheckBoxComputeConfirmationCodes);
			setDefaultNextStep(jCheckBoxAuditConfirmationCodes);
			return;
		}
		
		if ( ! new File(InputConstants.MeetingThreeOut).exists()) {
			setDefaultNextStep(jCheckBoxPublishResults);
			return;
		}

		if ( ! new File(InputConstants.MeetingFourIn).exists()) {
			setDefaultNextStep(jCheckBoxGenerateRandomChallengesM4);
			return;
		}

		if ( ! new File(InputConstants.MeetingFourOut).exists()) {
			setDefaultNextStep(jCheckBoxRunM4);
			setDefaultNextStep(jCheckBoxAuditM4);
			
			setDefaultNextStep(jCheckBoxPublishAllConfirmationCodesOnCastBallots);
			setDefaultNextStep(jCheckBoxAuditAllConfirmationCodesOnCastBallots);
			return;
		}
	}
	
	void setDefaultNextStep(JCheckBox jCheckBox) {
		jCheckBox.setSelected(true);
		
		Component parent=jCheckBox;
		while ( ! parent.getParent().getClass().getName().endsWith("JTabbedPane") && parent !=null) {
			parent=parent.getParent();
		}
		
		jTabbedPane.setSelectedComponent(parent);
	}
	
	boolean isLogedIn() {
		if (InputConstants.MK1 != null && InputConstants.MK2 !=null)
			return true;
		
		ElectionDataHandler edh = null;
		EnterPasswords ph = null;
        try
        {
        	File f=new File(InputConstants.privateFolder);
        	if (!f.exists())
        		f.mkdirs();
        		
            edh = new ElectionDataHandler(InputConstants.publicFolder, InputConstants.privateFolder, 1);
            WriteLog("Getting Passwords...\n");
            ph = new EnterPasswords(1, edh, this);
            ph.setModal(true);
            ph.setVisible(true);    
        }
        catch ( Exception ex )
        {
        	ex.printStackTrace();
            WriteLog("Error getting passwords: " +ex.getMessage());
            return false;
        }

        if (ph.isDone()) {
	        WriteLog("Processing Keys, Please Wait...\n");        
	        try
	        {
	            edh.ProcessKeys();
	        }
	        catch ( Exception ex )
	        {
	            WriteLog("Error processing keys: "+ ex.getMessage() + "\n" );
	            ex.printStackTrace();
	            return false;
	        }
	        WriteLog("Done Processing Keys");
	        
	        byte [] superKey = edh.getSuper();
	            
	        byte [] s1 = new byte[superKey.length/2];
	        byte [] s2 = new byte[superKey.length/2];
	        
	        System.arraycopy(superKey, 0, s1, 0, superKey.length/2);
	        System.arraycopy(superKey, superKey.length/2, s2, 0, superKey.length/2);
	    	
	        InputConstants.MK1=s1;
	        InputConstants.MK2=s2;
	        return true;    
        }
        return false;
	}
	
	void setAllCheckBoxes(boolean selected) {		
		try {
			Class<?> thisClass=Class.forName("software.engine.gui.ElectionConsole");
			for (Field field:thisClass.getDeclaredFields()) {
				if (field.getType().toString().trim().endsWith("JCheckBox")) {
					((JCheckBox)(field.get(this))).setSelected(selected);
				}
			}
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (SecurityException e) {
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		}
		
	}
	
	Vector<JCheckBox> getAllCheckBoxes() {
		Vector<JCheckBox> ret=new Vector<JCheckBox>();
		try {
			Class<?> thisClass=Class.forName("software.engine.gui.ElectionConsole");
			for (Field field:thisClass.getDeclaredFields()) {
				if (field.getType().toString().trim().endsWith("JCheckBox") && 
						((JCheckBox)(field.get(this))).isSelected()) {
					ret.add((JCheckBox)(field.get(this)));
				}
			}
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (SecurityException e) {
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		}
		return ret;
	}
	
	boolean permissionToWrite(String file) {
		if (overwriteExistingFiles)
			return true;
		
		File f=new File(file);
		if ( ! f.exists()) {
			f.getParentFile().mkdirs();
			return true;
		}
		
		Object[] options = {
                "Overwrite",
                "Overwrite All",
                "No"};
		int n = JOptionPane.showOptionDialog(this,
		"File "+file
		+ " already exists.\n Are you sure you want to overwrite it?",
		"A Silly Question",
		JOptionPane.YES_NO_CANCEL_OPTION,
		JOptionPane.QUESTION_MESSAGE,
		null,
		options,
		options[2]);

		if (n==2)
			return false;
		if (n==1)
			overwriteExistingFiles=true;
		return true;
	}
}
