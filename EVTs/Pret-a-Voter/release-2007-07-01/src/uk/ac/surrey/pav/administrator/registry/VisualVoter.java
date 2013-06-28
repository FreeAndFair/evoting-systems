package uk.ac.surrey.pav.administrator.registry;

import java.rmi.RemoteException;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;
import java.awt.event.KeyEvent;

/**
 * A visual representation of the voter and her ballot forms
 * 
 * @author David Lundin
 *
 */
public class VisualVoter extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;
	
	/**
	 * The voter we are dealing with here
	 */
	private Voter voter;

	/**
	 * The bulletin board server we are currently connected to
	 */
	private BulletinBoardInterface remoteBulletinBoard;

	private JLabel jLabelURNlabel = null;

	private JLabel jLabelNamelabel = null;

	private JLabel jLabelDOBlabel = null;

	private JLabel jLabelURN = null;

	private JLabel jLabelName = null;

	private JLabel jLabelDOB = null;

	private JButton jButtonAssignBallotForm = null;

	private JButton jButtonCancel = null;

	private JButton jButtonClose = null;

	private JScrollPane jScrollPaneBallotForms = null;

	private JTable jTableBallotForms = null;

	/**
	 * This is the default constructor
	 */
	public VisualVoter(JFrame parent, Voter voter, BulletinBoardInterface remoteBulletinBoard) {
		super();
		initialize();
		this.setLocationRelativeTo(parent);
		this.voter = voter;
		this.remoteBulletinBoard = remoteBulletinBoard;
		setout();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(713, 548);
		this.setTitle("Voter");
		this.setModal(true);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelDOB = new JLabel();
			jLabelDOB.setBounds(new java.awt.Rectangle(180,120,496,31));
			jLabelDOB.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 18));
			jLabelDOB.setText("");
			jLabelName = new JLabel();
			jLabelName.setBounds(new java.awt.Rectangle(180,75,496,31));
			jLabelName.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 18));
			jLabelName.setText("");
			jLabelURN = new JLabel();
			jLabelURN.setBounds(new java.awt.Rectangle(180,30,496,31));
			jLabelURN.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 18));
			jLabelURN.setText("");
			jLabelDOBlabel = new JLabel();
			jLabelDOBlabel.setBounds(new java.awt.Rectangle(30,120,136,31));
			jLabelDOBlabel.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelDOBlabel.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelDOBlabel.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jLabelDOBlabel.setText("Date of birth:");
			jLabelNamelabel = new JLabel();
			jLabelNamelabel.setBounds(new java.awt.Rectangle(30,75,136,31));
			jLabelNamelabel.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelNamelabel.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelNamelabel.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jLabelNamelabel.setText("Name:");
			jLabelURNlabel = new JLabel();
			jLabelURNlabel.setBounds(new java.awt.Rectangle(30,30,136,31));
			jLabelURNlabel.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelURNlabel.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelURNlabel.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jLabelURNlabel.setText("URN:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelURNlabel, null);
			jContentPane.add(jLabelNamelabel, null);
			jContentPane.add(jLabelDOBlabel, null);
			jContentPane.add(jLabelURN, null);
			jContentPane.add(jLabelName, null);
			jContentPane.add(jLabelDOB, null);
			jContentPane.add(getJButtonAssignBallotForm(), null);
			jContentPane.add(getJButtonCancel(), null);
			jContentPane.add(getJButtonClose(), null);
			jContentPane.add(getJScrollPaneBallotForms(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jButtonAssignBallotForm	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonAssignBallotForm() {
		if (jButtonAssignBallotForm == null) {
			jButtonAssignBallotForm = new JButton();
			jButtonAssignBallotForm.setBounds(new java.awt.Rectangle(30,420,196,61));
			jButtonAssignBallotForm.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jButtonAssignBallotForm.setMnemonic(KeyEvent.VK_A);
			jButtonAssignBallotForm.setText("Assign ballot form");
			jButtonAssignBallotForm.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					assignForm();
					
				}
			});
		}
		return jButtonAssignBallotForm;
	}

	/**
	 * This method initializes jButtonCancel	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCancel() {
		if (jButtonCancel == null) {
			jButtonCancel = new JButton();
			jButtonCancel.setBounds(new java.awt.Rectangle(255,420,196,61));
			jButtonCancel.setText("Cancel ballot form");
			jButtonCancel.setMnemonic(KeyEvent.VK_C);
			jButtonCancel.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					cancelForm();
					
				}
			});
		}
		return jButtonCancel;
	}

	/**
	 * This method initializes jButtonClose	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonClose() {
		if (jButtonClose == null) {
			jButtonClose = new JButton();
			jButtonClose.setBounds(new java.awt.Rectangle(480,420,196,61));
			jButtonClose.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jButtonClose.setMnemonic(KeyEvent.VK_L);
			jButtonClose.setText("Close");
			jButtonClose.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					close();
					
				}
			});
		}
		return jButtonClose;
	}

	/**
	 * This method initializes jScrollPaneBallotForms	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneBallotForms() {
		if (jScrollPaneBallotForms == null) {
			jScrollPaneBallotForms = new JScrollPane();
			jScrollPaneBallotForms.setBounds(new java.awt.Rectangle(30,180,646,211));
			jScrollPaneBallotForms.setViewportView(getJTableBallotForms());
		}
		return jScrollPaneBallotForms;
	}

	/**
	 * This method initializes jTableBallotForms	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableBallotForms() {
		if (jTableBallotForms == null) {
			jTableBallotForms = new JTable();
		}
		return jTableBallotForms;
	}
	
	/**
	 * Sets out the data items on the screen
	 *
	 */
	private void setout() {
		
		jLabelURN.setText(this.voter.urn);
		jLabelName.setText(this.voter.name);
		jLabelDOB.setText(this.voter.dob.toString());
		getJTableBallotForms().setModel(this.voter.getBallotFormList());
		if(this.voter.mayBeAssignedBallotForm() == true) {
			getJButtonAssignBallotForm().setEnabled(true);
			getJButtonCancel().setEnabled(false);
		} else {
			getJButtonAssignBallotForm().setEnabled(false);
			getJButtonCancel().setEnabled(true);
		}
		
	}
	
	/**
	 * Closes the modal window
	 *
	 */
	private void close() {
		this.setVisible(false);
	}
	
	private void assignForm() {
		
		int ballotFormID = Integer.parseInt(JOptionPane.showInputDialog(this, "Enter ballot form serial number:", "Assign", JOptionPane.QUESTION_MESSAGE));
		if(ballotFormID >= 1) {
			
			try {
				
				//Get from the wbb
				Voter newVoter = this.remoteBulletinBoard.assignFormToVoter(this.voter, ballotFormID);
				
				//Check if we got something back
				if(newVoter != null) {
					//We did, so went well
					
					//Store this new voter
					this.voter = newVoter;
					
					//Update the screen
					setout();
					
				} else {

					//This must have been something fishy
					JOptionPane.showMessageDialog(this, "This transaction could not be fulfilled as it appears illegal.", "Error", JOptionPane.ERROR_MESSAGE);

				}
				
			} catch (RemoteException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				JOptionPane.showMessageDialog(this, "Could not connect to the database. Please restart the application.", "Connection error", JOptionPane.ERROR_MESSAGE);
			}
			
		}

	}
	
	private void cancelForm() {
		
		Object[] options = {"YES, cancel ballot form", "NO, do not cancel ballot form"};
		int confirmation = JOptionPane.showOptionDialog(null, "Are you sure this ballot form should be cancelled?", "Please confirm", JOptionPane.DEFAULT_OPTION, JOptionPane.WARNING_MESSAGE, null, options, options[0]);
		if(confirmation == 0) {
		
			try {
				
				//Get from the wbb
				Voter newVoter = this.remoteBulletinBoard.cancelFormForVoter(this.voter);
				
				//Check if we got something back
				if(newVoter != null) {
					//We did, so went well
					
					//Store this new voter
					this.voter = newVoter;
					
					//Update the screen
					setout();
					
				} else {
	
					//This must have been something fishy
					JOptionPane.showMessageDialog(this, "This transaction could not be fulfilled as it appears illegal.", "Error", JOptionPane.ERROR_MESSAGE);
	
				}
				
			} catch (RemoteException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				JOptionPane.showMessageDialog(this, "Could not connect to the database. Please restart the application.", "Connection error", JOptionPane.ERROR_MESSAGE);
			}
			
		}
		
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
