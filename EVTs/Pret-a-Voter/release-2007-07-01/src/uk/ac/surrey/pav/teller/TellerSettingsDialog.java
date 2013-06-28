package uk.ac.surrey.pav.teller;

import java.io.FileInputStream;
import java.io.ObjectInputStream;
import java.security.PrivateKey;
import java.security.PublicKey;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JPasswordField;
import javax.swing.JTextField;
import java.awt.Dimension;
import java.awt.Rectangle;
import javax.swing.SwingConstants;

/**
 * Dialog window to enter or change settings for the teller
 * 
 * @author David Lundin
 *
 */
public class TellerSettingsDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;
	
	/**
	 * Old settings
	 */
	private TellerSettings oldSettings;
	
	/**
	 * New settings
	 */
	private TellerSettings newSettings = new TellerSettings();

	private JButton jButtonOK = null;

	private JButton jButtonCancel = null;

	private JButton jButtonLoadPrivateKey = null;

	private JLabel jLabelLoadPrivateKey = null;

	private JLabel jLabelServerAddress = null;

	private JLabel jLabelServerName = null;

	private JTextField jTextFieldServerAddress = null;

	private JTextField jTextFieldServerName = null;

	private JLabel jLabelBulletinBoardPublicKey = null;

	private JButton jButtonLoadBulletinBoardPublicKey = null;

	private JLabel jLabelDatabaseConnectionString = null;

	private JLabel jLabelDatabaseUsername = null;

	private JLabel jLabelDatabasePassword = null;

	private JTextField jTextFieldDatabaseConnectionString = null;

	private JTextField jTextFieldDatabaseUserName = null;

	private JPasswordField jPasswordFieldDatabasePassword = null;

	private JLabel jLabelBulletinBoardServerName = null;

	private JTextField jTextFieldBulletinBoardServerName = null;

	private JTextField jTextFieldBulletinBoardServerAddress = null;

	private JLabel jLabelBulletinBoardServerAddress = null;

	private JLabel jLabelTellerName = null;

	private JTextField jTextFieldTellerName = null;

	/**
	 * This is the default constructor
	 */
	public TellerSettingsDialog(TellerSettings oldSettings) {
		super();
		initialize();
		
		//Save reference to old settings
		this.oldSettings = oldSettings;
		
		//Create new settings
		this.newSettings.copySettings(this.oldSettings);

		//Set out the details
		getJTextFieldTellerName().setText(newSettings.getTellerName());
		if(newSettings.getPrivateKey() != null) {
			jLabelLoadPrivateKey.setText("Private key loaded.");
		} else {
			jLabelLoadPrivateKey.setText("No private key loaded.");
		}
		if(newSettings.getBulletinBoardPublicKey() != null) {
			jLabelBulletinBoardPublicKey.setText("Bulletin board public key.");
		} else {
			jLabelBulletinBoardPublicKey.setText("No bulletin board public key.");
		}
		getJTextFieldServerAddress().setText(newSettings.getServerAddress());
		getJTextFieldServerName().setText(newSettings.getServerName());
		getJTextFieldDatabaseConnectionString().setText(newSettings.getDatabaseConnectionString());
		getJTextFieldDatabaseUserName().setText(newSettings.getDatabaseUserName());
		getJPasswordFieldDatabasePassword().setText(newSettings.getDatabasePassword());
		getJTextFieldBulletinBoardServerAddress().setText(newSettings.getBulletinBoardServerAddress());
		getJTextFieldBulletinBoardServerName().setText(newSettings.getBulletinBoardServerName());
		
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(553, 586);
		this.setModal(true);
		this.setResizable(false);
		this.setTitle("Teller settings");
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelTellerName = new JLabel();
			jLabelTellerName.setBounds(new Rectangle(30, 120, 181, 31));
			jLabelTellerName.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelTellerName.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelTellerName.setText("Teller name:");
			jLabelBulletinBoardServerAddress = new JLabel();
			jLabelBulletinBoardServerAddress.setBounds(new Rectangle(30, 390, 181, 31));
			jLabelBulletinBoardServerAddress.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelBulletinBoardServerAddress.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelBulletinBoardServerAddress.setText("Bulletin board server address:");
			jLabelBulletinBoardServerName = new JLabel();
			jLabelBulletinBoardServerName.setBounds(new Rectangle(30, 435, 181, 31));
			jLabelBulletinBoardServerName.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelBulletinBoardServerName.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelBulletinBoardServerName.setText("Bulletin board server name:");
			jLabelDatabasePassword = new JLabel();
			jLabelDatabasePassword.setBounds(new Rectangle(30, 345, 181, 31));
			jLabelDatabasePassword.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelDatabasePassword.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelDatabasePassword.setText("Database password:");
			jLabelDatabaseUsername = new JLabel();
			jLabelDatabaseUsername.setBounds(new Rectangle(30, 300, 181, 31));
			jLabelDatabaseUsername.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelDatabaseUsername.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelDatabaseUsername.setText("Database user name:");
			jLabelDatabaseConnectionString = new JLabel();
			jLabelDatabaseConnectionString.setBounds(new Rectangle(30, 255, 181, 31));
			jLabelDatabaseConnectionString.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelDatabaseConnectionString.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelDatabaseConnectionString.setText("Database connection string:");
			jLabelBulletinBoardPublicKey = new JLabel();
			jLabelBulletinBoardPublicKey.setBounds(new java.awt.Rectangle(30,75,181,31));
			jLabelBulletinBoardPublicKey.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelBulletinBoardPublicKey.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelBulletinBoardPublicKey.setText("No bulletin board public key.");
			jLabelServerName = new JLabel();
			jLabelServerName.setBounds(new Rectangle(30, 210, 181, 31));
			jLabelServerName.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelServerName.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelServerName.setText("Teller server name:");
			jLabelServerAddress = new JLabel();
			jLabelServerAddress.setBounds(new Rectangle(30, 165, 181, 31));
			jLabelServerAddress.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelServerAddress.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelServerAddress.setText("Teller server address:");
			jLabelLoadPrivateKey = new JLabel();
			jLabelLoadPrivateKey.setBounds(new java.awt.Rectangle(30,30,181,31));
			jLabelLoadPrivateKey.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelLoadPrivateKey.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelLoadPrivateKey.setText("No private key loaded.");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJButtonCancel(), null);
			jContentPane.add(getJButtonLoadPrivateKey(), null);
			jContentPane.add(jLabelLoadPrivateKey, null);
			jContentPane.add(jLabelServerAddress, null);
			jContentPane.add(jLabelServerName, null);
			jContentPane.add(getJTextFieldServerAddress(), null);
			jContentPane.add(getJTextFieldServerName(), null);
			jContentPane.add(jLabelBulletinBoardPublicKey, null);
			jContentPane.add(getJButtonLoadBulletinBoardPublicKey(), null);
			jContentPane.add(jLabelDatabaseConnectionString, null);
			jContentPane.add(jLabelDatabaseUsername, null);
			jContentPane.add(jLabelDatabasePassword, null);
			jContentPane.add(getJTextFieldDatabaseConnectionString(), null);
			jContentPane.add(getJTextFieldDatabaseUserName(), null);
			jContentPane.add(getJPasswordFieldDatabasePassword(), null);
			jContentPane.add(jLabelBulletinBoardServerName, null);
			jContentPane.add(getJTextFieldBulletinBoardServerName(), null);
			jContentPane.add(getJTextFieldBulletinBoardServerAddress(), null);
			jContentPane.add(jLabelBulletinBoardServerAddress, null);
			jContentPane.add(jLabelTellerName, null);
			jContentPane.add(getJTextFieldTellerName(), null);
		}
		return jContentPane;
	}

	/**
	 * Loads a private key
	 *
	 */
	private void loadPrivateKey() {
		
		//Open a file
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				this.newSettings.setPrivateKey((PrivateKey)objectIn.readObject());
				jLabelLoadPrivateKey.setText("Private key loaded.");

		    } catch (Exception ex) {

				JOptionPane.showMessageDialog(this, "Unable to load the private key.", "Error", JOptionPane.ERROR_MESSAGE);
		    	
		    }

		}

	}

	private void loadPublicKey() {
		
		//Open a file
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				this.newSettings.setPublicKey((PublicKey)objectIn.readObject());
				jLabelBulletinBoardPublicKey.setText("Public key loaded.");

		    } catch (Exception ex) {

				JOptionPane.showMessageDialog(this, "Unable to load the public key.", "Error", JOptionPane.ERROR_MESSAGE);
		    	
		    }

		}

	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new Rectangle(360, 480, 106, 31));
			jButtonOK.setText("OK");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					saveSettings();
					
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
			jButtonCancel.setBounds(new Rectangle(240, 480, 106, 31));
			jButtonCancel.setText("Cancel");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					cancelSettings();
					
				}
			});
		}
		return jButtonCancel;
	}
	
	/**
	 * Closes the window without saving the settings
	 *
	 */
	private void cancelSettings() {
		
		//Close the window
		this.setVisible(false);
		
	}
	
	/**
	 * Saves the settings and closes the window
	 *
	 */
	private void saveSettings() {
		
		//Store the settings from the fields
		this.newSettings.setTellerName(getJTextFieldTellerName().getText());
		this.newSettings.setServerAddress(getJTextFieldServerAddress().getText());
		this.newSettings.setServerName(getJTextFieldServerName().getText());
		this.newSettings.setDatabaseConnectionString(getJTextFieldDatabaseConnectionString().getText());
		this.newSettings.setDatabaseUserName(getJTextFieldDatabaseUserName().getText());
		this.newSettings.setDatabasePassword(getJPasswordFieldDatabasePassword().getText());
		
		//Attempt connection to the database
		if(this.newSettings.connectToDatabase()) {
		
			if(this.newSettings.isProper()) {
				
				//Copy over the settings
				this.oldSettings.copySettings(newSettings);
				
				//Close the window
				this.setVisible(false);
	
			} else {
	
				JOptionPane.showMessageDialog(this, "Please give all the requested details.", "Error", JOptionPane.ERROR_MESSAGE);
	
			}
			
		} else {

			JOptionPane.showMessageDialog(this, "Unable to connect to the database.", "Error", JOptionPane.ERROR_MESSAGE);

		}
		
	}

	/**
	 * This method initializes jButtonLoadPrivateKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonLoadPrivateKey() {
		if (jButtonLoadPrivateKey == null) {
			jButtonLoadPrivateKey = new JButton();
			jButtonLoadPrivateKey.setBounds(new java.awt.Rectangle(225,30,106,31));
			jButtonLoadPrivateKey.setText("Load...");
			jButtonLoadPrivateKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					loadPrivateKey();
					
				}
			});
		}
		return jButtonLoadPrivateKey;
	}

	/**
	 * This method initializes jTextFieldServerAddress	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldServerAddress() {
		if (jTextFieldServerAddress == null) {
			jTextFieldServerAddress = new JTextField();
			jTextFieldServerAddress.setBounds(new Rectangle(225, 165, 241, 31));
			jTextFieldServerAddress.setText("");
		}
		return jTextFieldServerAddress;
	}

	/**
	 * This method initializes jTextFieldServerName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldServerName() {
		if (jTextFieldServerName == null) {
			jTextFieldServerName = new JTextField();
			jTextFieldServerName.setBounds(new Rectangle(225, 210, 241, 31));
		}
		return jTextFieldServerName;
	}

	/**
	 * This method initializes jButtonLoadBulletinBoardPublicKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonLoadBulletinBoardPublicKey() {
		if (jButtonLoadBulletinBoardPublicKey == null) {
			jButtonLoadBulletinBoardPublicKey = new JButton();
			jButtonLoadBulletinBoardPublicKey.setBounds(new java.awt.Rectangle(225,75,106,31));
			jButtonLoadBulletinBoardPublicKey.setText("Load...");
			jButtonLoadBulletinBoardPublicKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					loadPublicKey();
					
				}
			});
		}
		return jButtonLoadBulletinBoardPublicKey;
	}

	/**
	 * This method initializes jTextFieldDatabaseConnectionString	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldDatabaseConnectionString() {
		if (jTextFieldDatabaseConnectionString == null) {
			jTextFieldDatabaseConnectionString = new JTextField();
			jTextFieldDatabaseConnectionString.setBounds(new Rectangle(225, 255, 241, 31));
			jTextFieldDatabaseConnectionString.setText("");
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
			jTextFieldDatabaseUserName.setBounds(new Rectangle(225, 300, 241, 31));
			jTextFieldDatabaseUserName.setText("");
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
			jPasswordFieldDatabasePassword.setBounds(new Rectangle(225, 345, 241, 31));
		}
		return jPasswordFieldDatabasePassword;
	}

	/**
	 * This method initializes jTextFieldBulletinBoardServerName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldBulletinBoardServerName() {
		if (jTextFieldBulletinBoardServerName == null) {
			jTextFieldBulletinBoardServerName = new JTextField();
			jTextFieldBulletinBoardServerName.setBounds(new Rectangle(225, 435, 241, 31));
		}
		return jTextFieldBulletinBoardServerName;
	}

	/**
	 * This method initializes jTextFieldBulletinBoardServerAddress	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldBulletinBoardServerAddress() {
		if (jTextFieldBulletinBoardServerAddress == null) {
			jTextFieldBulletinBoardServerAddress = new JTextField();
			jTextFieldBulletinBoardServerAddress.setBounds(new Rectangle(225, 390, 241, 31));
		}
		return jTextFieldBulletinBoardServerAddress;
	}

	/**
	 * This method initializes jTextFieldTellerName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldTellerName() {
		if (jTextFieldTellerName == null) {
			jTextFieldTellerName = new JTextField();
			jTextFieldTellerName.setBounds(new Rectangle(225, 120, 241, 31));
		}
		return jTextFieldTellerName;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
