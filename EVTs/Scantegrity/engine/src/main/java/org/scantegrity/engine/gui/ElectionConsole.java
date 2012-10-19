package org.scantegrity.engine.gui;
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
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Calendar;
import java.util.Date;
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

import org.scantegrity.common.auditing.CheckTableCorrectness;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.authoring.invisibleink.PrintableBallotMakerWithBarcodes;
import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Util;
import org.scantegrity.engine.MeetingOne;
import org.scantegrity.engine.invisibleink.Test;


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
	private JTextField jTextFieldPDFFrom;
	private JLabel jLabelPDFFrom;
	private JPanel jPanel1;
	private JPanel jPanelPublishResults;
	private JPanel jPanelCheckSpoiledBallots;
	private JPanel jPanelRevealSpoiledBallots;
	private JPanel jPanelShowAllConfirmationCodes;
	private JPanel jPanelAuditConfirmationCodes;
	private JPanel jPanel3;
	private JPanel jPanelSpoiledBallots;
	private JCheckBox jCheckBoxGenerateRandomlySpoiledBallots;
	private JPanel jPanelGenerateRandomlySpoiledBallots;
	private JTextField jTextFieldNoWards;
	private JLabel jLabelNoWards;
	private JCheckBox jCheckBoxMailInBallots;
	private JCheckBox jCheckBoxInvisibleInkBallots;
	private JTextField jTextField2;
	private JLabel jLabel2;
	private JTextField jTextField1;
	private JLabel jLabel1;
	private JPanel jPanel2;
	private JPanel jPanelGenerateRandomlyVotedBallots;
	private JCheckBox jCheckBoxPublishAllConfirmationCodesOnCastBallots;
	private JCheckBox jCheckBoxAuditAllConfirmationCodesOnCastBallots;
	private JPanel jPanelPDFSerialNumbers;
	private JPanel jPanelGeneratePDFs;
	private JCheckBox jCheckBoxAuditM2;
	private JCheckBox jCheckBoxRunM2;
	private JCheckBox jCheckBoxGenerateRandomChallengesM2;
	private JPanel jPanelRunM2;
	private JPanel jPanelComputeConfirmationCodes;
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
	private JTextField jTextFieldPDFTo;
	private JLabel jLabelPDFTo;
	private JCheckBox jCheckBoxRunM1;
	private JPanel jPanelRunM1;
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

	//GUI elements for remotegrity ballot generation
	private JPanel jPanelRemotegrity;
	private JCheckBox jCheckBoxRemotegrityBallots;
	private JTextField jTextFieldRemotegrityStart;
	private JTextField jTextFieldRemotegrityEnd;
	private JLabel jLabelRemotegrityFrom;
	private JLabel jLabelRemotegrityTo;
	
	//GUI elements for accessbility ballot generation
	private JPanel jPanelAccessibility;
	private JCheckBox jCheckBoxAccessibilityBallots;
	private JTextField jTextFieldAccessibilityStart;
	private JTextField jTextFieldAccessibilityEnd;
	private JLabel jLabelAccessibilityFrom;
	private JLabel jLabelAccessibilityTo;

	

	
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
							//jPanelRunM2.add(jCheckBoxGenerateRandomChallengesM2);
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
							jPanelPDFSerialNumbers = new JPanel();
							FlowLayout jPanelPDFSerialNumbersLayout = new FlowLayout();
							jPanelPDFSerialNumbersLayout.setVgap(1);
							jPanelPDFSerialNumbers.setLayout(jPanelPDFSerialNumbersLayout);
							jPanelGeneratePDFs.add(jPanelPDFSerialNumbers);
							{
								jCheckBoxInvisibleInkBallots = new JCheckBox();
								jPanelPDFSerialNumbers.add(jCheckBoxInvisibleInkBallots);
								jCheckBoxInvisibleInkBallots.setText("Generate Polling Place Ballots");
							}
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
								jTextFieldPDFTo.setText("999");
								jTextFieldPDFTo
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
						}
						{
							jPanelRemotegrity = new JPanel();
							jPanelGeneratePDFs.add(jPanelRemotegrity);
							FlowLayout jPanelRemotegrityLayout = new FlowLayout();
							jPanelRemotegrityLayout.setVgap(1);
							jPanelRemotegrity.setLayout(jPanelRemotegrityLayout);
							{
								jCheckBoxRemotegrityBallots = new JCheckBox();
								jPanelRemotegrity.add(jCheckBoxRemotegrityBallots);
								jCheckBoxRemotegrityBallots.setText("Generate Remotegrity Ballots");
							}
							{
								jLabelRemotegrityFrom = new JLabel();
								jPanelRemotegrity.add(jLabelRemotegrityFrom);
								jLabelRemotegrityFrom.setText("From Serial No");
							}
							{
								jTextFieldRemotegrityStart = new JTextField();
								jPanelRemotegrity.add(jTextFieldRemotegrityStart);
								jTextFieldRemotegrityStart.setText("2000");
								jTextFieldRemotegrityStart
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
							{
								jLabelRemotegrityTo = new JLabel();
								jPanelRemotegrity.add(jLabelRemotegrityTo);
								jLabelRemotegrityTo.setText("To Serial No");
							}
							{
								jTextFieldRemotegrityEnd = new JTextField();
								jPanelRemotegrity.add(jTextFieldRemotegrityEnd);
								jTextFieldRemotegrityEnd.setText("2099");
								jTextFieldRemotegrityEnd
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
							{
								jPanelAccessibility = new JPanel();
								jPanelGeneratePDFs.add(jPanelAccessibility);
								FlowLayout jPanelAccessibilityLayout = new FlowLayout();
								jPanelAccessibilityLayout.setVgap(1);
								jPanelAccessibility.setLayout(jPanelAccessibilityLayout);
								{
									jCheckBoxAccessibilityBallots = new JCheckBox();
									jPanelAccessibility.add(jCheckBoxAccessibilityBallots);
									jCheckBoxAccessibilityBallots.setText("Generate Accessibility Ballots");
								}
								{
									jLabelAccessibilityFrom = new JLabel();
									jPanelAccessibility.add(jLabelAccessibilityFrom);
									jLabelAccessibilityFrom.setText("From Serial No");
								}
								{
									jTextFieldAccessibilityStart = new JTextField();
									jPanelAccessibility.add(jTextFieldAccessibilityStart);
									jTextFieldAccessibilityStart.setText("2100");
									jTextFieldAccessibilityStart
										.setPreferredSize(new java.awt.Dimension(
											45,
											20));
								}
								{
									jLabelAccessibilityTo = new JLabel();
									jPanelAccessibility.add(jLabelAccessibilityTo);
									jLabelAccessibilityTo.setText("To Serial No");
								}
								{
									jTextFieldAccessibilityEnd = new JTextField();
									jPanelAccessibility.add(jTextFieldAccessibilityEnd);
									jTextFieldAccessibilityEnd.setText("2199");
									jTextFieldAccessibilityEnd
										.setPreferredSize(new java.awt.Dimension(
											45,
											20));
								}
							}
						}
						{
							jPanel2 = new JPanel();
							jPanelGeneratePDFs.add(jPanel2);
							FlowLayout jPanel2Layout = new FlowLayout();
							jPanel2Layout.setVgap(1);
							jPanel2.setLayout(jPanel2Layout);
							{
								jCheckBoxMailInBallots = new JCheckBox();
								jPanel2.add(jCheckBoxMailInBallots);
								jCheckBoxMailInBallots.setText("Generate Plain B&W Ballots");
							}
							{
								jLabel1 = new JLabel();
								jPanel2.add(jLabel1);
								jLabel1.setText("From Serial No");
							}
							{
								jTextField1 = new JTextField();
								jPanel2.add(jTextField1);
								jTextField1.setText("2200");
								jTextField1
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
							{
								jLabel2 = new JLabel();
								jPanel2.add(jLabel2);
								jLabel2.setText("To Serial No");
							}
							{
								jTextField2 = new JTextField();
								jPanel2.add(jTextField2);
								jTextField2.setText("2299");
								jTextField2
									.setPreferredSize(new java.awt.Dimension(
										45,
										20));
							}
						}						
					}
				}
				{
					jPanelM3 = new JPanel();
					GridLayout jPanelMeetingThreeLayout = new GridLayout(7, 1);
					jPanelMeetingThreeLayout.setColumns(1);
					jPanelMeetingThreeLayout.setHgap(5);
					jPanelMeetingThreeLayout.setVgap(5);
					jPanelMeetingThreeLayout.setRows(7);
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
						//jPanelM3.add(jPanelGenerateRandomlyVotedBallots);
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
						jPanelGenerateRandomlySpoiledBallots = new JPanel();
						jPanelM3.add(jPanelGenerateRandomlySpoiledBallots);
						GridLayout jPanel3Layout = new GridLayout(1, 1);
						jPanel3Layout.setHgap(5);
						jPanel3Layout.setVgap(5);
						jPanel3Layout.setColumns(1);
						jPanelGenerateRandomlySpoiledBallots.setLayout(jPanel3Layout);
						{
							jCheckBoxGenerateRandomlySpoiledBallots = new JCheckBox();
							//jPanelGenerateRandomlySpoiledBallots.add(jCheckBoxGenerateRandomlySpoiledBallots);
							jCheckBoxGenerateRandomlySpoiledBallots.setText("Generate Randomly Spoiled Ballots");
							jCheckBoxGenerateRandomlySpoiledBallots.setForeground(new java.awt.Color(128,128,128));
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
							//jPanelRunM4.add(jCheckBoxGenerateRandomChallengesM4);
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
						jPanelSpoiledBallots = new JPanel();
						GridLayout jPanelSpoiledBallotsLayout = new GridLayout(
							4,
							1);
						jPanelSpoiledBallotsLayout.setHgap(5);
						jPanelSpoiledBallotsLayout.setVgap(5);
						jPanelSpoiledBallotsLayout.setColumns(1);
						jPanelSpoiledBallotsLayout.setRows(4);
						jPanelSpoiledBallots.setLayout(jPanelSpoiledBallotsLayout);
						jPanelM4.add(jPanelSpoiledBallots, BorderLayout.CENTER);
						{
							jPanelCheckSpoiledBallots = new JPanel();
							jPanelSpoiledBallots.add(jPanelCheckSpoiledBallots);
							GridLayout jPanelCheckSpoiledBallotsLayout = new GridLayout(
								1,
								1);
							jPanelCheckSpoiledBallotsLayout.setHgap(5);
							jPanelCheckSpoiledBallotsLayout.setVgap(5);
							jPanelCheckSpoiledBallotsLayout.setColumns(1);
							jPanelCheckSpoiledBallots
								.setLayout(jPanelCheckSpoiledBallotsLayout);
							{
								jCheckBoxCheckSpoiledBallots = new JCheckBox();
								jPanelCheckSpoiledBallots
									.add(jCheckBoxCheckSpoiledBallots);
								jCheckBoxCheckSpoiledBallots
									.setText("Check All the Print Audited Ballots");
							}
						}
						{
							jPanelRevealSpoiledBallots = new JPanel();
							jPanelSpoiledBallots.add(jPanelRevealSpoiledBallots);
							GridLayout jPanelRevealSpoiledBallotsLayout = new GridLayout(
								1,
								1);
							jPanelRevealSpoiledBallotsLayout.setHgap(5);
							jPanelRevealSpoiledBallotsLayout.setVgap(5);
							jPanelRevealSpoiledBallotsLayout.setColumns(1);
							jPanelRevealSpoiledBallots
								.setLayout(jPanelRevealSpoiledBallotsLayout);
							{
								jCheckBoxRevealSpoiledBallots = new JCheckBox();
								jPanelRevealSpoiledBallots
									.add(jCheckBoxRevealSpoiledBallots);
								jCheckBoxRevealSpoiledBallots
									.setText("Print audit all the ballots except the voted ones and the spoiled ones");
							}
						}
						{
							jPanel3 = new JPanel();
							jPanelSpoiledBallots.add(jPanel3);
							jPanel3.setPreferredSize(new java.awt.Dimension(787, 168));
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
								
								InputConstants.setPublicFolder(jTextFieldPublicFolder.getText()+Util.fileSeparator);
								//autoDetect();
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
								//selectFolder(JFileChooser.DIRECTORIES_ONLY,"Election Data Private Storage Location", InputConstants.privateFolder, jTextFieldPrivateFolder);
								//selectFolder(JFileChooser.DIRECTORIES_ONLY,"Election Data Private Storage Location", "C:/TP Nov 3 2009, mock PRIVATE/", jTextFieldPrivateFolder);
								selectFolder(JFileChooser.DIRECTORIES_ONLY,"Election Data Private Storage Location", "G:", jTextFieldPrivateFolder);
								
								InputConstants.setPrivateFolder(jTextFieldPrivateFolder.getText());
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
						jButtonGo.setPreferredSize(new java.awt.Dimension(168, 22));
						jButtonGo.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								go();
							}
						});
					}
					{
						jLabelNoWards = new JLabel();
						jPanelGo.add(jLabelNoWards);
						jLabelNoWards.setText("Number Of Wards");
					}
					{
						jTextFieldNoWards = new JTextField();
						jPanelGo.add(jTextFieldNoWards);
						jTextFieldNoWards.setText("6");
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
		StringBuffer sf=null;
        try {
        	int noWards=Integer.parseInt(jTextFieldNoWards.getText());
        	overwriteExistingFiles=false;
        	for (int ward=1;ward<=noWards;ward++) {
        		
        		InputConstants.setPublicFolder(jTextFieldPublicFolder.getText()+("ward"+ward)+Util.fileSeparator);
        		InputConstants.setPrivateFolder(jTextFieldPrivateFolder.getText()+("ward"+ward)+Util.fileSeparator);
        		
        		//autoDetect();
        		
            	sf=new StringBuffer();
            	sf.append("Executing: ");
            	for (JCheckBox jCheckBox:getAllCheckBoxes()) {
            		sf.append(jCheckBox.getText()+"\n");
            	}
            	WriteLog(sf.toString() + "\n");
        		
        		runMeetings();
        	}
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
        } catch (java.io.FileNotFoundException fileNotFounfEx) {        	
        	sf=new StringBuffer();
        	for (StackTraceElement s:fileNotFounfEx.getStackTrace()) {
        		sf.append(s+"\n");
        	}
            WriteLog("Error: File Not Found\n"+fileNotFounfEx+" thrown by \n"+sf.toString() + "\n");
            JOptionPane.showMessageDialog(this, "Error: File Not Found\n"+fileNotFounfEx, "Error", JOptionPane.ERROR_MESSAGE);
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
            JOptionPane.showMessageDialog(this, "Error Writing in the log file "+InputConstants.publicFolder + "/election.log", "Error", JOptionPane.ERROR_MESSAGE);    		
    	}
    	
        if ( jTextAreaLog != null )
        	jTextAreaLog.insert( output, jTextAreaLog.getText().length() );
        System.out.println( output );
        
        if (output.indexOf("has entered wrong user/pass")>0)
        	JOptionPane.showMessageDialog(this,  output, "Error", JOptionPane.ERROR_MESSAGE);

        //if (output.indexOf("Not Enough Passwords")>0)
        	//JOptionPane.showMessageDialog(this,  output, "Error", JOptionPane.ERROR_MESSAGE);
    }

    public void processKeys(int meeting) {
    	
    }
    
    void runMeetings() throws Exception {    	
    	try {
    		checkForM1In();
    	} catch (Exception e) {
    		Meeting1InputScreen inst = new Meeting1InputScreen(InputConstants.MeetingOneIn);
    		inst.setVisible(true);
    	}
    	
    	Test test=new Test();
    	if (jCheckBoxRunM1.isSelected() && permissionToWrite(InputConstants.MeetingOneOut) && isLogedIn(1)) {
    			test.testMeetingOne();
    	}
    	
    	if (jCheckBoxGenerateRandomChallengesM2.isSelected() && permissionToWrite(InputConstants.MeetingTwoIn)) {
    		MeetingOne m1=new MeetingOne(InputConstants.MeetingOneIn);

    		InputConstants.NoBallots=m1.getNumberOfBallots();
    		InputConstants.NoDs=m1.getNumberOfDs();
    		
    		test.testCreatetMeetingTwoInput();
    	}
    		
    	if (jCheckBoxRunM2.isSelected() && permissionToWrite(InputConstants.MeetingTwoOut)&& isLogedIn(2)) {
    			test.testMeetingTwo();
    	}
    	
    	if (jCheckBoxAuditM2.isSelected())
    		test.testPreElectionAudit();
    	
    	if (jCheckBoxInvisibleInkBallots.isSelected()) {    		
    		checkForM1In();
    		MeetingOne m1=new MeetingOne(InputConstants.MeetingOneIn);
    		
    		long start=System.currentTimeMillis();
    		//System.out.println("Starting to generate "+(Integer.parseInt(jTextFieldPDFTo.getText())-Integer.parseInt(jTextFieldPDFFrom.getText()))+" polling place ballots. Time "+(System.currentTimeMillis())+" meaning "+new Date());		

    		
    		ElectionSpecification es=m1.getEs();
    			//new ElectionSpecification(jTextFieldElectionSpec.getText());
    		BallotGeometry geom=new BallotGeometry(InputConstants.Geometry);

        	PrintableBallotMakerWithBarcodes pbm=new PrintableBallotMakerWithBarcodes(es,geom);
        	pbm.init(InputConstants.PdfTemplate,InputConstants.MeetingTwoPrints);
        	
        	//make ballots in batches
        	for (int i=Integer.parseInt(jTextFieldPDFFrom.getText());i<=Integer.parseInt(jTextFieldPDFTo.getText());i+=InputConstants.PrintBatchSize) {
        		pbm.makePrintableBallots(InputConstants.privateFolder, i,Math.min(i+InputConstants.PrintBatchSize-1, Integer.parseInt(jTextFieldPDFTo.getText())));	
        	}
    		//System.out.println("Finished generating "+(Integer.parseInt(jTextFieldPDFTo.getText())-Integer.parseInt(jTextFieldPDFFrom.getText()))+" polling place ballots. Time "+(System.currentTimeMillis())+" meaning "+new Date());		
        	
    		System.out.println("generating "+(Integer.parseInt(jTextFieldPDFTo.getText())-Integer.parseInt(jTextFieldPDFFrom.getText()))+" polling place ballots took "+((System.currentTimeMillis()-start))+" mseconds");		

    	}
    	
    	if (jCheckBoxRemotegrityBallots.isSelected()) {
    		checkForM1In();
    		MeetingOne m1=new MeetingOne(InputConstants.MeetingOneIn);
    		ElectionSpecification es=m1.getEs();
    		BallotGeometry geom=new BallotGeometry(InputConstants.Geometry);

        	PrintableBallotMakerWithBarcodes pbm=new PrintableBallotMakerWithBarcodes(es,geom);
        	pbm.init(InputConstants.PdfTemplate,InputConstants.MeetingTwoPrints);
        	pbm.makeRemotegrityBallots(InputConstants.privateFolder, Integer.parseInt(jTextFieldRemotegrityStart.getText()), Integer.parseInt(jTextFieldRemotegrityEnd.getText()));
    	}
    	
    	if (jCheckBoxAccessibilityBallots.isSelected())
    	{
    		checkForM1In();
    		MeetingOne m1=new MeetingOne(InputConstants.MeetingOneIn);
    		ElectionSpecification es=m1.getEs();
    		BallotGeometry geom=new BallotGeometry(InputConstants.Geometry);

        	PrintableBallotMakerWithBarcodes pbm=new PrintableBallotMakerWithBarcodes(es,geom);
        	pbm.init(InputConstants.PdfTemplate,InputConstants.MeetingTwoPrints);
        	pbm.makeAccessibilityBallots(InputConstants.privateFolder, Integer.parseInt(jTextFieldAccessibilityStart.getText()), Integer.parseInt(jTextFieldAccessibilityEnd.getText()));    		
    	}

    	if (jCheckBoxMailInBallots.isSelected()) {
    		checkForM1In();
    		MeetingOne m1=new MeetingOne(InputConstants.MeetingOneIn);

    		long start=System.currentTimeMillis();
    		//System.out.println("Starting to generate "+(Integer.parseInt(jTextFieldPDFTo.getText())-Integer.parseInt(jTextFieldPDFFrom.getText()))+" mail-in ballots. Time "+(System.currentTimeMillis())+" meaning "+new Date());		

    		
    		ElectionSpecification es=m1.getEs();
    			//new ElectionSpecification(jTextFieldElectionSpec.getText());
    		BallotGeometry geom=new BallotGeometry(InputConstants.Geometry);

        	PrintableBallotMakerWithBarcodes pbm=new PrintableBallotMakerWithBarcodes(es,geom);
        	pbm.init(InputConstants.PdfTemplate,InputConstants.MeetingTwoPrints);
        	pbm.mailIn=true;

        	//make ballots in batches
        	for (int i=Integer.parseInt(jTextField1.getText());i<=Integer.parseInt(jTextField2.getText());i+=InputConstants.PrintBatchSize) {
        		pbm.makePrintableBallots(InputConstants.privateFolder, i,Math.min(i+InputConstants.PrintBatchSize-1, Integer.parseInt(jTextField2.getText())));	
        	}

    		//System.out.println("Finished generating "+(Integer.parseInt(jTextFieldPDFTo.getText())-Integer.parseInt(jTextFieldPDFFrom.getText()))+" mail-in ballots. Time "+(System.currentTimeMillis())+" meaning "+new Date());		

    		System.out.println("generating "+(Integer.parseInt(jTextField2.getText())-Integer.parseInt(jTextField1.getText()))+" mail-in ballots took "+((System.currentTimeMillis()-start)/1000)+" seconds");		
    	}

    	
    	if (jCheckBoxGenerateRandomlyVotedBallots.isSelected() && permissionToWrite(InputConstants.BallotsDir) && isLogedIn(3)) {
    			test.testCreateRandomVotedBallots();
    	}
    	
    	if (jCheckBoxComputeConfirmationCodes.isSelected()) {
    		if (permissionToWrite(InputConstants.MeetingThreeOutCodes) && isLogedIn(3)) {
    			test.revealMarkedSymbols();
    		}
    	}
    	
    	if (jCheckBoxAuditConfirmationCodes.isSelected())
    		test.testAuditCodesForVotedCandidates();


    	if (jCheckBoxGenerateRandomlySpoiledBallots.isSelected() && permissionToWrite(InputConstants.PrintAuditCodes) && isLogedIn(3)) {
			test.testGenerateRandomSpoiledBallots();
    	}
    	
    	if (jCheckBoxRevealSpoiledBallots.isSelected() && permissionToWrite(InputConstants.PrintAuditCodes) && isLogedIn(3)) {
    			test.testRevealAuditedBallots();
    	}
    	
    	if (jCheckBoxCheckSpoiledBallots.isSelected()) {
    		test.testCheckAuditedBallots();
    	}
    	    	    	
    	if (jCheckBoxPublishResults.isSelected() && permissionToWrite(InputConstants.MeetingThreeOut) && isLogedIn(3)) {
    			test.computeResults();
    	}
    		
    	if (jCheckBoxGenerateRandomChallengesM4.isSelected() && permissionToWrite(InputConstants.MeetingFourIn)) {
    			test.testCreateMeetingFourInput();
    	}
    	
    	if (jCheckBoxRunM4.isSelected() && permissionToWrite(InputConstants.MeetingFourOut) && isLogedIn(4)) {
    			test.testMeetingFour();
    	}
    	
    	if (jCheckBoxAuditM4.isSelected())
    		test.testPostElectionAudit();
    	
    	if (jCheckBoxPublishAllConfirmationCodesOnCastBallots.isSelected() && permissionToWrite(InputConstants.ContestedCodes) && isLogedIn(4)) {
    			test.testChallengedCodes();
    	}
    		
    	if (jCheckBoxAuditAllConfirmationCodesOnCastBallots.isSelected()) {
    		test.testCodesCommitmentsAllCodesOnCastBallots();
    	}

    	//autoDetect();
    }
    
    void checkForM1In() throws Exception {
		try {
			Util.DomParse(InputConstants.MeetingOneIn);
		} catch (Exception e) {
			jPanelM1.requestFocus();
			throw e;
		}
    }
    			
	void autoDetect() {
    	setAllCheckBoxes(false);
		
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
	
	boolean isLogedIn(int meeting) throws Exception {
		if (InputConstants.MK1 != null && InputConstants.MK2 !=null)
			return true;
		
		ElectionDataHandler edh = null;
		EnterPasswords ph = null;
        //try
        {
        	File f=new File(InputConstants.privateFolder);
        	if (!f.exists())
        		f.mkdirs();
        		
            edh = new ElectionDataHandler(InputConstants.publicFolder, InputConstants.privateFolder, meeting);
            WriteLog("Getting Passwords...\n");
            ph = new EnterPasswords(meeting, edh, this);
            ph.setModal(true);
            ph.setVisible(true);    
        }
        //catch ( Exception ex )
        {
        	//ex.printStackTrace();
            //WriteLog("Error getting passwords: " +ex.getMessage());
            //return false;
        }

        if (ph.isDone()) {
	        WriteLog("Processing Keys, Please Wait...\n");
	        //try
	        {
	            edh.ProcessKeys();
	        }
	        //catch ( Exception ex )
	        {
	            //WriteLog("Error processing keys: "+ ex.getMessage() + "\n" );
	            //ex.printStackTrace();
	            //return false;
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
        } else {
            WriteLog("Error getting passwords: ");
            return false;
        }
	}
	
	void setAllCheckBoxes(boolean selected) {		
		try {
			Class<?> thisClass=Class.forName("org.scantegrity.engine.gui.ElectionConsole");
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
			Class<?> thisClass=Class.forName("org.scantegrity.engine.gui.ElectionConsole");
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
		"Overwrite?",
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
