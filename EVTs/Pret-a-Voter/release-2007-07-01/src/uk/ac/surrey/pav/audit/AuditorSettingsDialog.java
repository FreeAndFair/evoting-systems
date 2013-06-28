package uk.ac.surrey.pav.audit;

import javax.swing.JPanel;
import java.awt.Frame;
import javax.swing.JDialog;
import javax.swing.JLabel;
import java.awt.Rectangle;
import javax.swing.SwingConstants;
import javax.swing.JTextField;
import javax.swing.JPasswordField;
import javax.swing.JButton;

/**
 * Dialog box used to enter settings for the auditor
 * 
 * @author David Lundin
 *
 */
public class AuditorSettingsDialog extends JDialog {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;

	private JLabel jLabelDatabaseConnectionString = null;

	private JLabel jLabelDatabaseUserName = null;

	private JLabel jLabelDatabasePassword = null;

	private JTextField jTextFieldDatabaseConnectionString = null;

	private JTextField jTextFieldDatabaseUserName = null;

	private JPasswordField jPasswordFieldDatabasePassword = null;

	private JButton jButtonOK = null;

	private JButton jButtonCancel = null;
	
	/**
	 * Settings
	 */
	private AuditorSettings settings;

	/**
	 * @param owner
	 */
	public AuditorSettingsDialog(Frame owner, AuditorSettings settings) {
		super(owner);
		this.settings = settings;
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(512, 276);
		this.setModal(true);
		this.setTitle("Settings");
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelDatabasePassword = new JLabel();
			jLabelDatabasePassword.setBounds(new Rectangle(30, 120, 211, 31));
			jLabelDatabasePassword.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelDatabasePassword.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelDatabasePassword.setText("Database Password:");
			jLabelDatabaseUserName = new JLabel();
			jLabelDatabaseUserName.setBounds(new Rectangle(30, 75, 211, 31));
			jLabelDatabaseUserName.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelDatabaseUserName.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelDatabaseUserName.setText("Database User Name:");
			jLabelDatabaseConnectionString = new JLabel();
			jLabelDatabaseConnectionString.setBounds(new Rectangle(30, 30, 211, 31));
			jLabelDatabaseConnectionString.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelDatabaseConnectionString.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelDatabaseConnectionString.setText("Database Connection String:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelDatabaseConnectionString, null);
			jContentPane.add(jLabelDatabaseUserName, null);
			jContentPane.add(jLabelDatabasePassword, null);
			jContentPane.add(getJTextFieldDatabaseConnectionString(), null);
			jContentPane.add(getJTextFieldDatabaseUserName(), null);
			jContentPane.add(getJPasswordFieldDatabasePassword(), null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJButtonCancel(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jTextFieldDatabaseConnectionString	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldDatabaseConnectionString() {
		if (jTextFieldDatabaseConnectionString == null) {
			jTextFieldDatabaseConnectionString = new JTextField();
			jTextFieldDatabaseConnectionString.setBounds(new Rectangle(255, 30, 211, 31));
			jTextFieldDatabaseConnectionString.setText(this.settings.getDatabaseConnectionString());
		}
		return jTextFieldDatabaseConnectionString;
	}

	/**
	 * This method initializes jTextFieldDatabaseUserName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldDatabaseUserName() {
		if (jTextFieldDatabaseUserName == null) {
			jTextFieldDatabaseUserName = new JTextField();
			jTextFieldDatabaseUserName.setBounds(new Rectangle(255, 75, 211, 31));
			jTextFieldDatabaseUserName.setText(this.settings.getDatabaseUserName());
		}
		return jTextFieldDatabaseUserName;
	}

	/**
	 * This method initializes jPasswordFieldDatabasePassword	
	 * 	
	 * @return javax.swing.JPasswordField	
	 */
	private JPasswordField getJPasswordFieldDatabasePassword() {
		if (jPasswordFieldDatabasePassword == null) {
			jPasswordFieldDatabasePassword = new JPasswordField();
			jPasswordFieldDatabasePassword.setBounds(new Rectangle(255, 120, 211, 31));
			jPasswordFieldDatabasePassword.setText(this.settings.getDatabasePassword());
		}
		return jPasswordFieldDatabasePassword;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new Rectangle(345, 180, 121, 31));
			jButtonOK.setText("OK");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					saveSettingsAndClose();
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
			jButtonCancel.setBounds(new Rectangle(210, 180, 121, 31));
			jButtonCancel.setText("Cancel");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					closeWindow();
				}
			});
		}
		return jButtonCancel;
	}
	
	private void closeWindow() {
		this.dispose();
	}
	
	private void saveSettingsAndClose() {
		
		//Store the new settings
		this.settings.setDatabaseConnectionString(getJTextFieldDatabaseConnectionString().getText());
		this.settings.setDatabaseUserName(getJTextFieldDatabaseUserName().getText());
		this.settings.setDatabasePassword(getJPasswordFieldDatabasePassword().getText());
		
		//Close the window
		this.dispose();
		
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
