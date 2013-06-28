package uk.ac.surrey.pav.tools;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JPanel;

/**
 * Tools for dealing with RSA key pairs
 * 
 * @author David Lundin
 *
 */
public class KeyPairCreator extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	private JButton jButtonSaveKeyPair = null;
	private JButton jButtonSavePrivateKey = null;
	private JButton jButtonSavePublicKey = null;
	private JButton jButtonGenerateKeyPair = null;
	private JButton jButtonLoadKeyPair = null;
	
	/**
	 * The key pair being worked on
	 */
	private KeyPair keyPair;

	/**
	 * This method initializes jButtonSaveKeyPair	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSaveKeyPair() {
		if (jButtonSaveKeyPair == null) {
			jButtonSaveKeyPair = new JButton();
			jButtonSaveKeyPair.setBounds(new java.awt.Rectangle(345,15,151,46));
			jButtonSaveKeyPair.setEnabled(false);
			jButtonSaveKeyPair.setText("Save Key Pair");
			jButtonSaveKeyPair.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					saveObject(keyPair);
				}
			});
		}
		return jButtonSaveKeyPair;
	}

	/**
	 * This method initializes jButtonSavePrivateKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSavePrivateKey() {
		if (jButtonSavePrivateKey == null) {
			jButtonSavePrivateKey = new JButton();
			jButtonSavePrivateKey.setBounds(new java.awt.Rectangle(345,75,151,46));
			jButtonSavePrivateKey.setEnabled(false);
			jButtonSavePrivateKey.setText("Save Private Key");
			jButtonSavePrivateKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					saveObject(keyPair.getPrivate());
				}
			});
		}
		return jButtonSavePrivateKey;
	}

	/**
	 * This method initializes jButtonSavePublicKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSavePublicKey() {
		if (jButtonSavePublicKey == null) {
			jButtonSavePublicKey = new JButton();
			jButtonSavePublicKey.setBounds(new java.awt.Rectangle(345,135,151,46));
			jButtonSavePublicKey.setEnabled(false);
			jButtonSavePublicKey.setText("Save Public Key");
			jButtonSavePublicKey.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					saveObject(keyPair.getPublic());
				}
			});
		}
		return jButtonSavePublicKey;
	}

	/**
	 * This method initializes jButtonGenerateKeyPair	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonGenerateKeyPair() {
		if (jButtonGenerateKeyPair == null) {
			jButtonGenerateKeyPair = new JButton();
			jButtonGenerateKeyPair.setBounds(new java.awt.Rectangle(15,15,151,46));
			jButtonGenerateKeyPair.setText("Generate KeyPair");
			jButtonGenerateKeyPair.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					try {
						//Generate key pair
						KeyPairGenerator keyGen = KeyPairGenerator.getInstance("RSA");
						keyPair = keyGen.generateKeyPair();
						
						//Enable buttons
						getJButtonSaveKeyPair().setEnabled(true);
						getJButtonSavePrivateKey().setEnabled(true);
						getJButtonSavePublicKey().setEnabled(true);
					} catch (Exception ex) {
						handleError();
						ex.printStackTrace();
					}

				}
			});
		}
		return jButtonGenerateKeyPair;
	}

	/**
	 * This method initializes jButtonLoadKeyPair	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonLoadKeyPair() {
		if (jButtonLoadKeyPair == null) {
			jButtonLoadKeyPair = new JButton();
			jButtonLoadKeyPair.setBounds(new java.awt.Rectangle(180,15,151,46));
			jButtonLoadKeyPair.setEnabled(true);
			jButtonLoadKeyPair.setText("Load KeyPair");
			jButtonLoadKeyPair.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					//Open a file
					JFileChooser jfc = new JFileChooser();
					if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
						try {
							
							//Load key pair
							ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
							keyPair = ((KeyPair)objectIn.readObject());

							//Enable buttons
							getJButtonSaveKeyPair().setEnabled(true);
							getJButtonSavePrivateKey().setEnabled(true);
							getJButtonSavePublicKey().setEnabled(true);

					    } catch (Exception ex) {
					    	handleError();
					    	ex.printStackTrace();
					    }

					}

				}
			});
		}
		return jButtonLoadKeyPair;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		(new KeyPairCreator()).setVisible(true);
	}

	/**
	 * This is the default constructor
	 */
	public KeyPairCreator() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(518, 234);
		this.setContentPane(getJContentPane());
		this.setTitle("RSA Key Tools");
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
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(getJButtonSaveKeyPair(), null);
			jContentPane.add(getJButtonSavePrivateKey(), null);
			jContentPane.add(getJButtonSavePublicKey(), null);
			jContentPane.add(getJButtonGenerateKeyPair(), null);
			jContentPane.add(getJButtonLoadKeyPair(), null);
		}
		return jContentPane;
	}
	
	private void handleError() {
		keyPair = null;
		getJButtonSaveKeyPair().setEnabled(false);
		getJButtonSavePrivateKey().setEnabled(false);
		getJButtonSavePublicKey().setEnabled(false);
	}
	
	private void saveObject(Object object) {
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectOutputStream objectOut = new ObjectOutputStream(new FileOutputStream(jfc.getSelectedFile()));
				objectOut.writeObject(object);

		    } catch (IOException e) {
		    	e.printStackTrace();
		    	handleError();
		    }

		}

	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
