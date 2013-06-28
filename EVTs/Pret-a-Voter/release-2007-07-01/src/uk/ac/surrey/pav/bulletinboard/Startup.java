package uk.ac.surrey.pav.bulletinboard;

import java.awt.Rectangle;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.util.Properties;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JPasswordField;
import javax.swing.JTextField;
import javax.swing.SwingConstants;
import javax.swing.JCheckBox;
import java.awt.Dimension;

/**
 * Welcome screen that accepts database connection information from the user
 * 
 * @author David Lundin
 *
 */
public class Startup extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabelURL = null;
	private JTextField jTextFieldURL = null;
	private JLabel jLabelUserName = null;
	private JLabel jLabelPassword = null;
	private JTextField jTextFieldUsername = null;
	private JPasswordField jPasswordField = null;
	private JLabel jLabelHeader = null;
	private JButton jButtonOK = null;
	private JButton jButtonCancel = null;

	private JLabel jLabelCopyright = null;
	
	/**
	 * A bulletin board that is to be populated from the database
	 */
	private BulletinBoard bulletinBoard;
	
	/**
	 * Temporary storage for the private key that has been loaded
	 */
	private PrivateKey privateKey;
	
	/**
	 * Temporary storage for the public key of the administrator
	 */
	private PublicKey administratorPublicKey;

	private JLabel jLabelPrivateKey = null;

	private JButton jButtonPrivateKey = null;

	private JLabel jLabelPublicKey = null;

	private JButton jButtonPublicKey = null;

	private JCheckBox jCheckBoxStorePassword = null;

	/**
	 * This is the default constructor
	 */
	public Startup() {
		super();
		initialize();
		
		try {

			//Load settings file
			Properties props = new Properties();
	        props.load(Class.class.getResourceAsStream("/uk/ac/surrey/pav/bulletinboard/BulletinBoard.prop"));
	        
	        //Set the field contents
			this.getJTextFieldURL().setText(props.getProperty("dbconnstring"));
			this.getJTextFieldUsername().setText(props.getProperty("dbusername"));
			this.getJPasswordField().setText(props.getProperty("dbpassword"));

		} catch (IOException e) {
			
			//Could not load settings from file
			
		}
		
		try {

			//Load bulletin board private key from file
			ObjectInputStream objectIn = new ObjectInputStream(Class.class.getResourceAsStream("/uk/ac/surrey/pav/bulletinboard/BulletinBoard_private_key.ppk"));
			this.privateKey = (PrivateKey)objectIn.readObject();
			
		} catch (ClassNotFoundException e) {
			
			//Could not load key from file
			
		} catch (IOException e) {
			
			//Coule not load key from file
			
		}

		try {

			//Load administrator public key from file
			ObjectInputStream objectIn = new ObjectInputStream(Class.class.getResourceAsStream("/uk/ac/surrey/pav/bulletinboard/Administrator_public_key.ppk"));
			this.administratorPublicKey = (PublicKey)objectIn.readObject();

		} catch (ClassNotFoundException e) {
			
			//Could not load key from file
			
		} catch (IOException e) {
			
			//Coule not load key from file
			
		}

	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(517, 486);
		this.setResizable(false);
		this.setContentPane(getJContentPane());
		this.setTitle("Prêt à Voter: Web Bulletin Board");
		this.addWindowListener(new java.awt.event.WindowAdapter() {
			public void windowClosing(java.awt.event.WindowEvent e) {
				System.exit(0);
			}
		});
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelPublicKey = new JLabel();
			jLabelPublicKey.setBounds(new Rectangle(60, 300, 91, 31));
			jLabelPublicKey.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelPublicKey.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelPublicKey.setText("Public key:");
			jLabelPrivateKey = new JLabel();
			jLabelPrivateKey.setBounds(new Rectangle(60, 255, 91, 31));
			jLabelPrivateKey.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelPrivateKey.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelPrivateKey.setText("Private key:");
			jLabelCopyright = new JLabel();
			jLabelCopyright.setBounds(new java.awt.Rectangle(60,60,391,31));
			jLabelCopyright.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelCopyright.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelCopyright.setText("Developed by the E-Voting Group, University of Surrey, UK");
			jLabelHeader = new JLabel();
			jLabelHeader.setBounds(new java.awt.Rectangle(60,30,391,31));
			jLabelHeader.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelHeader.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelHeader.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 18));
			jLabelHeader.setText("Welcome to Prêt à Voter");
			jLabelPassword = new JLabel();
			jLabelPassword.setBounds(new java.awt.Rectangle(60,195,92,31));
			jLabelPassword.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelPassword.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelPassword.setText("Password:");
			jLabelUserName = new JLabel();
			jLabelUserName.setBounds(new java.awt.Rectangle(60,150,92,31));
			jLabelUserName.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelUserName.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelUserName.setText("User name:");
			jLabelURL = new JLabel();
			jLabelURL.setBounds(new java.awt.Rectangle(60,105,92,31));
			jLabelURL.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelURL.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelURL.setText("Database URL:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelURL, null);
			jContentPane.add(getJTextFieldURL(), null);
			jContentPane.add(jLabelUserName, null);
			jContentPane.add(jLabelPassword, null);
			jContentPane.add(getJTextFieldUsername(), null);
			jContentPane.add(getJPasswordField(), null);
			jContentPane.add(jLabelHeader, null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJButtonCancel(), null);
			jContentPane.add(jLabelCopyright, null);
			jContentPane.add(jLabelPrivateKey, null);
			jContentPane.add(getJButtonPrivateKey(), null);
			jContentPane.add(jLabelPublicKey, null);
			jContentPane.add(getJButtonPublicKey(), null);
			jContentPane.add(getJCheckBoxStorePassword(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jTextFieldURL	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldURL() {
		if (jTextFieldURL == null) {
			jTextFieldURL = new JTextField();
			jTextFieldURL.setBounds(new java.awt.Rectangle(165,105,286,31));
			jTextFieldURL.setText("");
		}
		return jTextFieldURL;
	}

	/**
	 * This method initializes jTextFieldUsername	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldUsername() {
		if (jTextFieldUsername == null) {
			jTextFieldUsername = new JTextField();
			jTextFieldUsername.setBounds(new java.awt.Rectangle(165,150,286,31));
			jTextFieldUsername.setText("");
		}
		return jTextFieldUsername;
	}

	/**
	 * This method initializes jPasswordField	
	 * 	
	 * @return javax.swing.JPasswordField	
	 */
	private JPasswordField getJPasswordField() {
		if (jPasswordField == null) {
			jPasswordField = new JPasswordField();
			jPasswordField.setBounds(new java.awt.Rectangle(165,195,285,31));
			jPasswordField.setText("");
		}
		return jPasswordField;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new Rectangle(345, 375, 106, 31));
			jButtonOK.setText("OK");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					loadFromDatabase();
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
			jButtonCancel.setBounds(new Rectangle(225, 375, 106, 31));
			jButtonCancel.setText("Cancel");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					System.exit(0);
				}
			});
		}
		return jButtonCancel;
	}

	/**
	 * Shows the load from database dialog and then checks if there is a connection
	 *
	 */
	private void loadFromDatabase() {
		
		if(this.privateKey != null && this.administratorPublicKey != null) {

			//Create a new bulletin board object
			bulletinBoard = new BulletinBoard(this.privateKey, this.administratorPublicKey);
			
			//Show the database connection window modally
			new DatabaseConnectorDialog(bulletinBoard, getJTextFieldURL().getText(), getJTextFieldUsername().getText(), getJPasswordField().getText());
			
			//Store settings in prop file
			try {
				
				//Load settings file
				Properties props = new Properties();
		        props.load(Class.class.getResourceAsStream("/uk/ac/surrey/pav/bulletinboard/BulletinBoard.prop"));
		        
		        //Insert settings
		        props.setProperty("dbconnstring", this.getJTextFieldURL().getText());
		        props.setProperty("dbusername", this.getJTextFieldUsername().getText());
		        
		        if(this.getJCheckBoxStorePassword().isSelected()) {
		        	props.setProperty("dbpassword", this.getJPasswordField().getText());
		        }

			} catch (IOException e) {
				
				//Could not update settings file
				e.printStackTrace();
				
			}
			
			//If there is a connection now then we can proceed, otherwise do nothing
			if(bulletinBoard.testConnection()) {
				
				//There is a connection, go to next step
				(new Dashboard(bulletinBoard)).setVisible(true);
				this.setVisible(false);
				
			} else {
				
				//There is no connection so do nothing
				System.out.println("Failed to open database etc.");
				
			}
			
		} else {
			
			JOptionPane.showMessageDialog(this, "Please load a private key and an administrator public key before proceeding.", "Error", JOptionPane.ERROR_MESSAGE);
			
		}

	}
	
	/**
	 * This method initializes jButtonPrivateKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonPrivateKey() {
		if (jButtonPrivateKey == null) {
			jButtonPrivateKey = new JButton();
			jButtonPrivateKey.setBounds(new Rectangle(165, 255, 286, 31));
			jButtonPrivateKey.setActionCommand("");
			jButtonPrivateKey.setText("Load web bulletin board's private key...");
			jButtonPrivateKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					loadPrivateKey();
				}
			});
		}
		return jButtonPrivateKey;
	}

	/**
	 * Loads a private key into temporary storage
	 *
	 */
	private void loadPrivateKey() {

		//Open a file
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				this.privateKey = ((PrivateKey)objectIn.readObject());

		    } catch (Exception ex) {

				JOptionPane.showMessageDialog(this, "Private key could not be loaded", "Error", JOptionPane.ERROR_MESSAGE);
		    	this.privateKey = null;
		    	
		    }

		}

	}
	
	/**
	 * Loads the administrators public key from a file
	 *
	 */
	private void loadAdministratorPublicKey() {

		//Open a file
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				this.administratorPublicKey = ((PublicKey)objectIn.readObject());

		    } catch (Exception ex) {

				JOptionPane.showMessageDialog(this, "Private key could not be loaded", "Error", JOptionPane.ERROR_MESSAGE);
		    	this.administratorPublicKey = null;
		    	
		    }

		}

	}

	/**
	 * This method initializes jButtonPublicKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonPublicKey() {
		if (jButtonPublicKey == null) {
			jButtonPublicKey = new JButton();
			jButtonPublicKey.setBounds(new Rectangle(165, 300, 286, 31));
			jButtonPublicKey.setText("Load administrator's public key...");
			jButtonPublicKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					loadAdministratorPublicKey();
					
				}
			});
		}
		return jButtonPublicKey;
	}

	/**
	 * This method initializes jCheckBoxStorePassword	
	 * 	
	 * @return javax.swing.JCheckBox	
	 */
	private JCheckBox getJCheckBoxStorePassword() {
		if (jCheckBoxStorePassword == null) {
			jCheckBoxStorePassword = new JCheckBox();
			jCheckBoxStorePassword.setBounds(new Rectangle(285, 228, 166, 23));
			jCheckBoxStorePassword.setHorizontalAlignment(SwingConstants.RIGHT);
			jCheckBoxStorePassword.setHorizontalTextPosition(SwingConstants.RIGHT);
			jCheckBoxStorePassword.setSelected(true);
			jCheckBoxStorePassword.setText("Store the password");
		}
		return jCheckBoxStorePassword;
	}

	/**
	 * Runs the application
	 * 
	 * @param args No arguments
	 */
	public static void main(String[] args) {
		//Show a database connect window
		(new Startup()).setVisible(true);
	}
}  //  @jve:decl-index=0:visual-constraint="10,10"
