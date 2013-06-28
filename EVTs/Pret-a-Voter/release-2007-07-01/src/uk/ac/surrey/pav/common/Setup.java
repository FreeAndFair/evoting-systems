package uk.ac.surrey.pav.common;

import java.io.FileInputStream;
import java.io.ObjectInputStream;
import java.security.PrivateKey;

import javax.swing.JFileChooser;
import javax.swing.JPanel;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JButton;
import javax.swing.JTextField;

/**
 * A graphical user interface to accept settings for various clients
 * 
 * @author David Lundin
 *
 */
public class Setup extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	private JLabel jLabelPrivateKey = null;
	private JButton jButtonLoadPrivateKey = null;
	private JLabel jLabelBulletinBoardAddress = null;
	private JLabel jLabelBulletinBoardName = null;
	private JTextField jTextFieldBulletinBoardAddress = null;
	private JTextField jTextFieldBulletinBoardName = null;
	private JButton jButtonOK = null;
	
	/**
	 * Settings
	 */
	private ClientSettings newSettings = new ClientSettings();
	private ClientSettings oldSettings;
	private JButton jButtonExit = null;
	private JButton jButtonCancel = null;
	private JLabel jLabelID = null;
	private JTextField jTextFieldID = null;

	/**
	 * This is the default constructor
	 */
	public Setup(ClientSettings settings) {
		super();
		
		//Store reference to old settings and copy them over
		oldSettings = settings;
		newSettings.copySettings(oldSettings);
		
		initialize();

		//Show old settings in boxes
		if(oldSettings.isProperSettings()) {
			getJTextFieldID().setText("" + oldSettings.ID);
			jLabelPrivateKey.setText("Private key loaded.");
			getJTextFieldBulletinBoardAddress().setText(oldSettings.bulletinBoardAddress);
			getJTextFieldBulletinBoardName().setText(oldSettings.bulletinBoardName);
		}
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(439, 300);
		this.setTitle("Settings");
		this.setResizable(false);
		this.setModal(true);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setContentPane(getJContentPane());
		
		//Check if Cancel button should be enabled
		if(oldSettings.isProperSettings()) {
			getJButtonCancel().setEnabled(true);
		} else {
			getJButtonCancel().setEnabled(false);
		}
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelID = new JLabel();
			jLabelID.setBounds(new java.awt.Rectangle(30,15,181,31));
			jLabelID.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelID.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelID.setText("My ID:");
			jLabelBulletinBoardName = new JLabel();
			jLabelBulletinBoardName.setBounds(new java.awt.Rectangle(30,150,181,31));
			jLabelBulletinBoardName.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelBulletinBoardName.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelBulletinBoardName.setText("Bulletin board server name:");
			jLabelBulletinBoardAddress = new JLabel();
			jLabelBulletinBoardAddress.setBounds(new java.awt.Rectangle(30,105,181,31));
			jLabelBulletinBoardAddress.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelBulletinBoardAddress.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelBulletinBoardAddress.setText("Bulletin board address:");
			jLabelPrivateKey = new JLabel();
			jLabelPrivateKey.setBounds(new java.awt.Rectangle(30,60,181,31));
			jLabelPrivateKey.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelPrivateKey.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelPrivateKey.setText("No private key loaded");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelPrivateKey, null);
			jContentPane.add(getJButtonLoadPrivateKey(), null);
			jContentPane.add(jLabelBulletinBoardAddress, null);
			jContentPane.add(jLabelBulletinBoardName, null);
			jContentPane.add(getJTextFieldBulletinBoardAddress(), null);
			jContentPane.add(getJTextFieldBulletinBoardName(), null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJButtonExit(), null);
			jContentPane.add(getJButtonCancel(), null);
			jContentPane.add(jLabelID, null);
			jContentPane.add(getJTextFieldID(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jButtonLoadPrivateKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonLoadPrivateKey() {
		if (jButtonLoadPrivateKey == null) {
			jButtonLoadPrivateKey = new JButton();
			jButtonLoadPrivateKey.setBounds(new java.awt.Rectangle(225,60,181,31));
			jButtonLoadPrivateKey.setText("Load...");
			jButtonLoadPrivateKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					//Open a file
					JFileChooser jfc = new JFileChooser();
					if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
						try {
							
							ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
							newSettings.privateKey = ((PrivateKey)objectIn.readObject());
							jLabelPrivateKey.setText("Private key loaded.");

					    } catch (Exception ex) {

					    	jLabelPrivateKey.setText("ERROR: No private key has been loaded.");
					    	newSettings.privateKey = null;
							jLabelPrivateKey.setText("No private key loaded.");
					    	ex.printStackTrace();
					    	
					    }

					}

				}
			});
		}
		return jButtonLoadPrivateKey;
	}

	/**
	 * This method initializes jTextFieldBulletinBoardAddress	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldBulletinBoardAddress() {
		if (jTextFieldBulletinBoardAddress == null) {
			jTextFieldBulletinBoardAddress = new JTextField();
			jTextFieldBulletinBoardAddress.setBounds(new java.awt.Rectangle(225,105,181,31));
			jTextFieldBulletinBoardAddress.setText("127.0.0.1");
		}
		return jTextFieldBulletinBoardAddress;
	}

	/**
	 * This method initializes jTextFieldBulletinBoardName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldBulletinBoardName() {
		if (jTextFieldBulletinBoardName == null) {
			jTextFieldBulletinBoardName = new JTextField();
			jTextFieldBulletinBoardName.setBounds(new java.awt.Rectangle(225,150,181,31));
			jTextFieldBulletinBoardName.setText("Bulletinboard");
		}
		return jTextFieldBulletinBoardName;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new java.awt.Rectangle(315,210,91,31));
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
	 * Stores settings and closes window
	 *
	 */
	private void saveSettings() {
		
		//Store the text variables
		this.newSettings.ID = Integer.parseInt(getJTextFieldID().getText());
		this.newSettings.bulletinBoardAddress = getJTextFieldBulletinBoardAddress().getText();
		this.newSettings.bulletinBoardName = getJTextFieldBulletinBoardName().getText();

		//Check if all settings are ok
		if(this.newSettings.isProperSettings()) {
				
			//Copy over the settings
			this.oldSettings.copySettings(this.newSettings);

			//Close the window
			this.setVisible(false);
				
		}
		
	}

	/**
	 * This method initializes jButtonExit	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonExit() {
		if (jButtonExit == null) {
			jButtonExit = new JButton();
			jButtonExit.setBounds(new java.awt.Rectangle(30,210,91,31));
			jButtonExit.setText("Exit");
			jButtonExit.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					System.exit(0);
				}
			});
		}
		return jButtonExit;
	}

	/**
	 * This method initializes jButtonCancel	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCancel() {
		if (jButtonCancel == null) {
			jButtonCancel = new JButton();
			jButtonCancel.setBounds(new java.awt.Rectangle(210,210,91,31));
			jButtonCancel.setText("Cancel");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					notSaveSettings();
				}
			});
		}
		return jButtonCancel;
	}
	
	/**
	 * Exits without saving
	 *
	 */
	private void notSaveSettings() {
		//Hide the window
		this.setVisible(false);
	}

	/**
	 * This method initializes jTextFieldID	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldID() {
		if (jTextFieldID == null) {
			jTextFieldID = new JTextField();
			jTextFieldID.setBounds(new java.awt.Rectangle(225,15,181,31));
			jTextFieldID.setText("5");
		}
		return jTextFieldID;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
