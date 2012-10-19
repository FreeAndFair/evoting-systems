package org.scantegrity.auditor.gui;
import java.awt.BorderLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.IOException;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import javax.swing.WindowConstants;

import org.scantegrity.common.auditing.CheckBallotDecryption;
import org.scantegrity.common.auditing.CheckTableCorrectness;

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

/**
 * Asks for the io of all four meetings and runs the two auditors
 */
public class ElectionAudit extends javax.swing.JFrame {
	private static final long serialVersionUID = 6001764402771003436L;
	private JPanel jPanelMain;
	private JTextField jTextFieldMeetingTwoIn;
	private JLabel jLabelMeetingTwoIn;
	private JButton jButtonMeetingOneOut;
	private JTextField jTextFieldMeetingOneOut;
	private JLabel jLabelMeetingOneOut;
	private JButton jButtonMeetingOneIn;
	private JTextField jTextFieldMeetingOneIn;
	private JLabel jLabelMeetingOneIn;
	private JButton jButtonCancel;
	private JButton jButtonMeetingTwoOut;
	private JButton jButtonPostElectionAudit;
	private JButton jButtonMeetingFourOut;
	private JTextField jTextFieldMeetingFourOut;
	private JLabel jLabelMeetingFourOut;
	private JButton jButtonMeetingFourIn;
	private JTextField jTextFieldMeetingFourIn;
	private JTextField jTextFieldMeetingThreeOut;
	private JLabel jLabelMeetingFourIn;
	private JButton jButtonMeetingThreeOut;
	private JLabel jLabelMeetingThreeOut;
	private JButton jButtonMeetingThreeIn;
	private JTextField jTextFieldMeetingThreeIn;
	private JLabel jLabelMeetingThreeIn;
	private JTextField jTextFieldMeetingTwoOut;
	private JLabel jLabelMeetingTwoOut;
	private JButton jButtonMeetingTwoIn;
	private JButton jButtonPreElectionAudit;
	private JPanel jPanelOkCancelButtons;
	private JPanel jPanelFiles;

	JFileChooser jFileChooser=new JFileChooser(".");
	/**
	* Auto-generated main method to display this JFrame
	*/
	public static void main(String[] args) {
		ElectionAudit inst = new ElectionAudit();
		inst.setVisible(true);
	}
	
	public ElectionAudit() {
		super();
		initGUI();
	}
	
	private void initGUI() {
		try {
			setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
			addWindowListener( new WindowAdapter() {
				   public void windowClosing( WindowEvent e ){
					   cancel();
				   }
			} ); 			

			{
				jPanelMain = new JPanel();
				BorderLayout jPanelMainLayout = new BorderLayout();
				jPanelMain.setLayout(jPanelMainLayout);
				getContentPane().add(jPanelMain, BorderLayout.CENTER);
				{
					jPanelFiles = new JPanel();
					GridLayout jPanelFilesLayout = new GridLayout(8, 3);
					jPanelFilesLayout.setHgap(5);
					jPanelFilesLayout.setVgap(5);
					jPanelFilesLayout.setColumns(3);
					jPanelFilesLayout.setRows(8);
					jPanelFiles.setLayout(jPanelFilesLayout);
					jPanelMain.add(jPanelFiles, BorderLayout.CENTER);
					{
						jLabelMeetingOneIn = new JLabel();
						jPanelFiles.add(jLabelMeetingOneIn);
						jLabelMeetingOneIn.setText("MeetingOneIn");
					}
					{
						jTextFieldMeetingOneIn = new JTextField();
						jPanelFiles.add(jTextFieldMeetingOneIn);
						jTextFieldMeetingOneIn
							.setText("public/MeetingOneIn.xml");
					}
					{
						jButtonMeetingOneIn = new JButton();
						jPanelFiles.add(jButtonMeetingOneIn);
						jButtonMeetingOneIn.setText("Browse");
						jButtonMeetingOneIn
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingOneIn.xml",jTextFieldMeetingOneIn);
							}
							});
					}
					{
						jLabelMeetingOneOut = new JLabel();
						jPanelFiles.add(jLabelMeetingOneOut);
						jLabelMeetingOneOut.setText("MeetingOneOut");
					}
					{
						jTextFieldMeetingOneOut = new JTextField();
						jPanelFiles.add(jTextFieldMeetingOneOut);
						jTextFieldMeetingOneOut.setText("public/MeetingOneOut");
					}
					{
						jButtonMeetingOneOut = new JButton();
						jPanelFiles.add(jButtonMeetingOneOut);
						jButtonMeetingOneOut.setText("Browse");
						jButtonMeetingOneOut
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingOneOut.xml",jTextFieldMeetingOneOut);							}
							});
					}
					{
						jLabelMeetingTwoIn = new JLabel();
						jPanelFiles.add(jLabelMeetingTwoIn);
						jLabelMeetingTwoIn.setText("MeetingTwoIn");
					}
					{
						jTextFieldMeetingTwoIn = new JTextField();
						jPanelFiles.add(jTextFieldMeetingTwoIn);
						jTextFieldMeetingTwoIn.setText("public/MeetingTwoIn");
					}
					{
						jButtonMeetingTwoIn = new JButton();
						jPanelFiles.add(jButtonMeetingTwoIn);
						jButtonMeetingTwoIn.setText("Browse");
						jButtonMeetingTwoIn
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingTwoIn.xml",jTextFieldMeetingTwoIn);							}
							});
					}
					{
						jLabelMeetingTwoOut = new JLabel();
						jPanelFiles.add(jLabelMeetingTwoOut);
						jLabelMeetingTwoOut.setText("MeetingTwoOut");
					}
					{
						jTextFieldMeetingTwoOut = new JTextField();
						jPanelFiles.add(jTextFieldMeetingTwoOut);
						jTextFieldMeetingTwoOut.setText("public/MeetingTwoOut");
					}
					{
						jButtonMeetingTwoOut = new JButton();
						jPanelFiles.add(jButtonMeetingTwoOut);
						jButtonMeetingTwoOut.setText("Browse");
						jButtonMeetingTwoOut
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingTwoOut.xml",jTextFieldMeetingTwoOut);							}
							});
					}
					{
						jLabelMeetingThreeIn = new JLabel();
						jPanelFiles.add(jLabelMeetingThreeIn);
						jLabelMeetingThreeIn.setText("MeetingThreeIn");
					}
					{
						jTextFieldMeetingThreeIn = new JTextField();
						jPanelFiles.add(jTextFieldMeetingThreeIn);
						jTextFieldMeetingThreeIn
							.setText("public/MeetingThreeIn");
					}
					{
						jButtonMeetingThreeIn = new JButton();
						jPanelFiles.add(jButtonMeetingThreeIn);
						jButtonMeetingThreeIn.setText("Browse");
						jButtonMeetingThreeIn
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingThreeIn.xml", jTextFieldMeetingThreeIn);
							}
							});
					}
					{
						jLabelMeetingThreeOut = new JLabel();
						jPanelFiles.add(jLabelMeetingThreeOut);
						jLabelMeetingThreeOut.setText("MeetingThreeOut");
					}
					{
						jTextFieldMeetingThreeOut = new JTextField();
						jPanelFiles.add(jTextFieldMeetingThreeOut);
						jTextFieldMeetingThreeOut
							.setText("public/MeetingThreeOut");
					}
					{
						jButtonMeetingThreeOut = new JButton();
						jPanelFiles.add(jButtonMeetingThreeOut);
						jButtonMeetingThreeOut.setText("Browse");
						jButtonMeetingThreeOut
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingThreeOut.xml", jTextFieldMeetingThreeOut);
							}
							});
					}
					{
						jLabelMeetingFourIn = new JLabel();
						jPanelFiles.add(jLabelMeetingFourIn);
						jLabelMeetingFourIn.setText("MeetingFourIn");
					}
					{
						jTextFieldMeetingFourIn = new JTextField();
						jPanelFiles.add(jTextFieldMeetingFourIn);
						jTextFieldMeetingFourIn.setText("public/MeetingFourIn");
					}
					{
						jButtonMeetingFourIn = new JButton();
						jPanelFiles.add(jButtonMeetingFourIn);
						jButtonMeetingFourIn.setText("Browse");
						jButtonMeetingFourIn
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingFourIn.xml", jTextFieldMeetingFourIn);							}
							});
					}
					{
						jLabelMeetingFourOut = new JLabel();
						jPanelFiles.add(jLabelMeetingFourOut);
						jLabelMeetingFourOut.setText("MeetingFourOut");
					}
					{
						jTextFieldMeetingFourOut = new JTextField();
						jPanelFiles.add(jTextFieldMeetingFourOut);
						jTextFieldMeetingFourOut
							.setText("public/MeetingFourOut");
					}
					{
						jButtonMeetingFourOut = new JButton();
						jPanelFiles.add(jButtonMeetingFourOut);
						jButtonMeetingFourOut.setText("Browse");
						jButtonMeetingFourOut
							.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browse("MeetingFourOut.xml", jTextFieldMeetingFourOut);							}
							});
					}
				}
				{
					jPanelOkCancelButtons = new JPanel();
					jPanelMain.add(jPanelOkCancelButtons, BorderLayout.SOUTH);
					jPanelOkCancelButtons.setPreferredSize(new java.awt.Dimension(392, 35));
					{
						jButtonPreElectionAudit = new JButton();
						jPanelOkCancelButtons.add(jButtonPreElectionAudit);
						jButtonPreElectionAudit.setText("PreElection Audit");
						jButtonPreElectionAudit.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								runPreElectionAudit();
							}
						});
					}
					{
						jButtonPostElectionAudit = new JButton();
						jPanelOkCancelButtons.add(jButtonPostElectionAudit);
						jButtonPostElectionAudit.setText("PostEelectionAudit");
						jButtonPostElectionAudit
							.addActionListener(new ActionListener() {
								public void actionPerformed(ActionEvent evt) {
									runPostElectionAudit();
								}
							});
					}
					{
						jButtonCancel = new JButton();
						jPanelOkCancelButtons.add(jButtonCancel);
						jButtonCancel.setText("Cancel");
						jButtonCancel.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								cancel();
							}
						});
					}					
				}
			}
			pack();
			setSize(400, 300);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private void browse(String dialog,JTextField textFieldToSet) {
    	jFileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
    	jFileChooser.setDialogTitle(dialog);
    	try {
    		jFileChooser.setSelectedFile(new File(dialog));
    	} catch (Exception e) {
    		
    	}
    	jFileChooser.setVisible(true);
        int retVal = jFileChooser.showOpenDialog(this);
        if (retVal == JFileChooser.APPROVE_OPTION)
        {
            try {
            	textFieldToSet.setText(jFileChooser.getSelectedFile().getCanonicalPath());
			} catch (IOException e) {
				e.printStackTrace();
			}                                         
        }
        else
        {
            return;
        }		
	}
	
	private void cancel() {
		this.setVisible(false);
		dispose();
		System.exit(-1);
	}
	
	private void runPreElectionAudit() {
		CheckTableCorrectness ctc;
		try {
			ctc = new CheckTableCorrectness(
					jTextFieldMeetingOneIn.getText(),
					jTextFieldMeetingTwoIn.getText(),
					jTextFieldMeetingTwoOut.getText());
			ctc.check(jTextFieldMeetingOneOut.getText());
		} catch (Exception e) {
			e.printStackTrace();
			JOptionPane.showMessageDialog(this,
					"The auditor failed\n" +
					"Error:"+e.getMessage(),
					"Error",
					JOptionPane.ERROR_MESSAGE);
			return;
		} 
		JOptionPane.showMessageDialog(this, "The auditor was succesful");
	}
	
	private void runPostElectionAudit() {
		CheckBallotDecryption cbd;
		try {
			cbd = new CheckBallotDecryption(
					jTextFieldMeetingOneIn.getText(),
					jTextFieldMeetingThreeIn.getText(),
					jTextFieldMeetingThreeOut.getText(),
					jTextFieldMeetingFourIn.getText(),
					jTextFieldMeetingFourOut.getText());
			cbd.check(jTextFieldMeetingOneOut.getText());
		} catch (Exception e) {
			e.printStackTrace();
			JOptionPane.showMessageDialog(this,
					"The auditor failed\n" +
					"Error:"+e.getMessage(),
					"Error",
					JOptionPane.ERROR_MESSAGE);
			return;
		} 
		JOptionPane.showMessageDialog(this, "The auditor was succesful");
	}
	
}
