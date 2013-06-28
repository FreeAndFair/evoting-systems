package uk.ac.surrey.pav.administrator;

import java.awt.Frame;
import java.io.FileInputStream;
import java.io.ObjectInputStream;
import java.security.PublicKey;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import uk.ac.surrey.pav.administrator.treenodes.Teller;

/**
 * Used to get information about a teller that is added or edited
 * from the user.
 * 
 * @author David Lundin
 *
 */
public class NewEntityDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabelName = null;
	private JTextField jTextFieldName = null;
	private JLabel jLabelPublicKey = null;
	private JButton jButtonPrivateKey = null;
	private JButton jButtonOK = null;
	private JButton jButtonCancel = null;
	
	/**
	 * The teller object passed to the dialog
	 */
	private EditableEntity oldTeller;
	
	/**
	 * The new public key to load into the object
	 */
	private PublicKey newPublicKey;

	private JLabel jLabelID = null;

	private JTextField jTextFieldID = null;

	private JLabel jLabelIPAddress = null;

	private JTextField jTextFieldIPAdress = null;

	private JLabel jLabelServerName = null;

	private JTextField jTextFieldServerName = null;

	/**
	 * This is the default constructor
	 */
	public NewEntityDialog(EditableEntity oldTeller) {
		super();
		
		//Reference to the old teller
		this.oldTeller = oldTeller;
		
		//Initialise
		initialize();
		
		//Blank out those fields not needed
		if(!(this.oldTeller instanceof Teller)) {
			//This is not a teller and thus blank some out
			jLabelIPAddress.setEnabled(false);
			getJTextFieldIPAdress().setEnabled(false);
			jLabelServerName.setEnabled(false);
			getJTextFieldServerName().setEnabled(false);
		}
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(413, 362);
		this.setModal(true);
		this.setTitle("Add/Edit");
		this.setResizable(false);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelServerName = new JLabel();
			jLabelServerName.setBounds(new java.awt.Rectangle(30,210,91,31));
			jLabelServerName.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelServerName.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelServerName.setText("Server name:");
			jLabelIPAddress = new JLabel();
			jLabelIPAddress.setBounds(new java.awt.Rectangle(30,165,91,31));
			jLabelIPAddress.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelIPAddress.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelIPAddress.setText("IP address:");
			jLabelID = new JLabel();
			jLabelID.setBounds(new java.awt.Rectangle(30,30,91,31));
			jLabelID.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelID.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelID.setText("ID:");
			jLabelPublicKey = new JLabel();
			jLabelPublicKey.setBounds(new java.awt.Rectangle(30,120,91,31));
			jLabelPublicKey.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelPublicKey.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelPublicKey.setText("Public key:");
			jLabelName = new JLabel();
			jLabelName.setBounds(new java.awt.Rectangle(30,75,91,31));
			jLabelName.setHorizontalAlignment(javax.swing.SwingConstants.RIGHT);
			jLabelName.setHorizontalTextPosition(javax.swing.SwingConstants.RIGHT);
			jLabelName.setText("Name:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelName, null);
			jContentPane.add(getJTextFieldName(), null);
			jContentPane.add(jLabelPublicKey, null);
			jContentPane.add(getJButtonPrivateKey(), null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJButtonCancel(), null);
			jContentPane.add(jLabelID, null);
			jContentPane.add(getJTextFieldID(), null);
			jContentPane.add(jLabelIPAddress, null);
			jContentPane.add(getJTextFieldIPAdress(), null);
			jContentPane.add(jLabelServerName, null);
			jContentPane.add(getJTextFieldServerName(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jTextFieldName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldName() {
		if (jTextFieldName == null) {
			jTextFieldName = new JTextField();
			jTextFieldName.setBounds(new java.awt.Rectangle(135,75,241,31));
			jTextFieldName.setText(oldTeller.getName());
		}
		return jTextFieldName;
	}

	/**
	 * This method initializes jButtonPrivateKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonPrivateKey() {
		if (jButtonPrivateKey == null) {
			jButtonPrivateKey = new JButton();
			jButtonPrivateKey.setBounds(new java.awt.Rectangle(135,120,106,31));
			jButtonPrivateKey.setText("Load...");
			jButtonPrivateKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					loadPublicKey();
					
				}
			});
		}
		return jButtonPrivateKey;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new java.awt.Rectangle(180,270,91,31));
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
			jButtonCancel.setBounds(new java.awt.Rectangle(285,270,91,31));
			jButtonCancel.setText("Cancel");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					dialogExit();
					
				}
			});
		}
		return jButtonCancel;
	}
	
	/**
	 * Close the dialog box without storing anything entered in the boxes
	 *
	 */
	private void dialogExit() {
		
		this.setVisible(false);
		
	}
	
	/**
	 * Update the teller object and then close dialog box
	 *
	 */
	private void dialogOK() {
		
		//Check if we have everything we need
		if(((!(this.oldTeller instanceof Teller)) || (getJTextFieldIPAdress().getText().length() > 0 && getJTextFieldServerName().getText().length() > 0))
			&& this.jTextFieldName.getText().length() > 0 && (this.newPublicKey != null || this.oldTeller.hasPublicKey())) {
			
			//We do have everything we need, set
			this.oldTeller.setID(Integer.parseInt(this.jTextFieldID.getText()));
			this.oldTeller.setName(this.jTextFieldName.getText());
			
			//Check if there is a new public key
			if(this.newPublicKey != null) {
				
				//We do want to store the new public key
				this.oldTeller.setPublicKey(this.newPublicKey);
				
			}
			
			//If this is a Teller...
			if(this.oldTeller instanceof Teller) {
				//...also set the IP address and server name
				
				this.oldTeller.setIPAddress(getJTextFieldIPAdress().getText());
				this.oldTeller.setServerName(getJTextFieldServerName().getText());
				
			}
			
			//Hide box
			this.setVisible(false);

		} else {
			
			//Dialog box to say that something is missing
			JOptionPane.showMessageDialog(this, "All fields (including public key) must be entered.", "Error", JOptionPane.ERROR_MESSAGE);
			
		}
		
		
	}
	
	/**
	 * Loads a public key
	 *
	 */
	private void loadPublicKey() {

		//Open a file
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				this.newPublicKey = ((PublicKey)objectIn.readObject());

		    } catch (Exception ex) {

				JOptionPane.showMessageDialog(this, "Public key could not be loaded", "Error", JOptionPane.ERROR_MESSAGE);
				this.newPublicKey = null;
		    	
		    }

		}

	}

	/**
	 * This method initializes jTextFieldID	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldID() {
		if (jTextFieldID == null) {
			jTextFieldID = new JTextField();
			jTextFieldID.setBounds(new java.awt.Rectangle(135,30,241,31));
			if(oldTeller.getID() >= 0) {
				jTextFieldID.setText(Integer.toString(oldTeller.getID()));
			}
		}
		return jTextFieldID;
	}

	/**
	 * This method initializes jTextFieldIPAdress	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldIPAdress() {
		if (jTextFieldIPAdress == null) {
			jTextFieldIPAdress = new JTextField();
			jTextFieldIPAdress.setBounds(new java.awt.Rectangle(135,165,241,31));
			jTextFieldIPAdress.setText(oldTeller.getIPAddress());
		}
		return jTextFieldIPAdress;
	}

	/**
	 * This method initializes jTextFieldServerName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldServerName() {
		if (jTextFieldServerName == null) {
			jTextFieldServerName = new JTextField();
			jTextFieldServerName.setBounds(new java.awt.Rectangle(135,210,241,31));
			jTextFieldServerName.setText(oldTeller.getServerName());
		}
		return jTextFieldServerName;
	}


}  //  @jve:decl-index=0:visual-constraint="10,10"
