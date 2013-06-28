package uk.ac.surrey.pav.administrator;

import java.awt.Rectangle;
import java.sql.Date;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.SwingConstants;

import uk.ac.surrey.pav.administrator.treenodes.Election;

/**
 * Dialog box that allows the user to input values needed to construct a new election
 * 
 * @author David Lundin
 *
 */
public class NewElectionDialog extends JDialog {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;

	private JLabel jLabelElectionName = null;

	private JLabel jLabelElectionStartDate = null;

	private JLabel jLabelElectionEndDate = null;

	private JTextField jTextFieldElectionName = null;

	private JTextField jTextFieldElectionStartDate = null;

	private JTextField jTextFieldElectionEndDate = null;

	private JButton jButtonOK = null;

	private JButton jButtonCancel = null;
	
	/**
	 * Reference to old election
	 */
	private Election oldElection;

	/**
	 * Constructor
	 * 
	 * @param oldElection The old election object
	 */
	public NewElectionDialog(Election oldElection) {
		super();
		
		//Store reference to old election
		this.oldElection = oldElection;
		
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(399, 274);
		this.setModal(true);
		this.setTitle("Add/Edit election");
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelElectionEndDate = new JLabel();
			jLabelElectionEndDate.setBounds(new Rectangle(30, 120, 121, 31));
			jLabelElectionEndDate.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelElectionEndDate.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelElectionEndDate.setText("Election End:");
			jLabelElectionStartDate = new JLabel();
			jLabelElectionStartDate.setBounds(new Rectangle(30, 75, 121, 31));
			jLabelElectionStartDate.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelElectionStartDate.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelElectionStartDate.setText("Election Start:");
			jLabelElectionName = new JLabel();
			jLabelElectionName.setBounds(new Rectangle(30, 30, 121, 31));
			jLabelElectionName.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelElectionName.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelElectionName.setText("Name of Election:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelElectionName, null);
			jContentPane.add(jLabelElectionStartDate, null);
			jContentPane.add(jLabelElectionEndDate, null);
			jContentPane.add(getJTextFieldElectionName(), null);
			jContentPane.add(getJTextFieldElectionStartDate(), null);
			jContentPane.add(getJTextFieldElectionEndDate(), null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJButtonCancel(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jTextFieldElectionName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldElectionName() {
		if (jTextFieldElectionName == null) {
			jTextFieldElectionName = new JTextField();
			jTextFieldElectionName.setBounds(new Rectangle(165, 30, 196, 31));
			jTextFieldElectionName.setText(oldElection.getName());
		}
		return jTextFieldElectionName;
	}

	/**
	 * This method initializes jTextFieldElectionStartDate	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldElectionStartDate() {
		if (jTextFieldElectionStartDate == null) {
			jTextFieldElectionStartDate = new JTextField();
			jTextFieldElectionStartDate.setBounds(new Rectangle(165, 75, 196, 31));
			jTextFieldElectionStartDate.setText(oldElection.getStartDate().toString());
		}
		return jTextFieldElectionStartDate;
	}

	/**
	 * This method initializes jTextFieldElectionEndDate	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldElectionEndDate() {
		if (jTextFieldElectionEndDate == null) {
			jTextFieldElectionEndDate = new JTextField();
			jTextFieldElectionEndDate.setBounds(new Rectangle(165, 120, 196, 31));
			jTextFieldElectionEndDate.setText(oldElection.getEndDate().toString());
		}
		return jTextFieldElectionEndDate;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new Rectangle(165, 180, 91, 31));
			jButtonOK.setText("OK");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					dialogOK();
					
				}
			});
		}
		return jButtonOK;
	}

	/**
	 * This method initializes jButtonCancel	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCancel() {
		if (jButtonCancel == null) {
			jButtonCancel = new JButton();
			jButtonCancel.setBounds(new Rectangle(270, 180, 91, 31));
			jButtonCancel.setText("Cancel");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					dialogCancel();
					
				}
			});
		}
		return jButtonCancel;
	}
	
	private void dialogOK() {
		
		//Check if we have everything we need
		if(getJTextFieldElectionName().getText().length() > 0
				&& getJTextFieldElectionStartDate().getText().length() > 0
				&& getJTextFieldElectionEndDate().getText().length() > 0) {
			
			//Set everything
			this.oldElection.setName(getJTextFieldElectionName().getText());
			this.oldElection.setStartDate(Date.valueOf(getJTextFieldElectionStartDate().getText()));
			this.oldElection.setEndDate(Date.valueOf(getJTextFieldElectionEndDate().getText()));
			
			//Hide box
			this.setVisible(false);

		} else {
			
			//Dialog box to say that something is missing
			JOptionPane.showMessageDialog(this, "All fields are mandatory.", "Error", JOptionPane.ERROR_MESSAGE);
			
		}

	}
	
	/**
	 * Cancels the input
	 *
	 */
	private void dialogCancel() {
		
		this.setVisible(false);
		
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
