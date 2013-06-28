package uk.ac.surrey.pav.teller;

import java.awt.Rectangle;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.UnsupportedEncodingException;
import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.Signature;
import java.security.SignatureException;
import java.util.Properties;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;
import java.awt.Dimension;

/**
 * Graphical user interface for the Teller server
 * 
 * @author David Lundin
 *
 */
public class TellerGUI extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;
	
	/**
	 * Settings for the teller
	 */
	TellerSettings settings = new TellerSettings();
	
	/**
	 * A teller server
	 */
	TellerServer server;

	private JScrollPane jScrollPaneTellerStatus = null;

	private JTable jTableTellerStatus = null;

	private JButton jButtonExit = null;

	private JLabel jLabelTitle = null;

	private JButton jButtonStart = null;

	private JButton jButtonStop = null;

	private JButton jButtonSettings = null;

	private JButton jButtonIdentifyToBulletinBoard = null;

	/**
	 * This method initializes jScrollPaneTellerStatus	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneTellerStatus() {
		if (jScrollPaneTellerStatus == null) {
			jScrollPaneTellerStatus = new JScrollPane();
			jScrollPaneTellerStatus.setBounds(new Rectangle(30, 75, 481, 271));
			jScrollPaneTellerStatus.setViewportView(getJTableTellerStatus());
		}
		return jScrollPaneTellerStatus;
	}

	/**
	 * This method initializes jTableTellerStatus	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableTellerStatus() {
		if (jTableTellerStatus == null) {
			jTableTellerStatus = new JTable(new TellerTableModel(settings));
		}
		return jTableTellerStatus;
	}

	/**
	 * This method initializes jButtonExit	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonExit() {
		if (jButtonExit == null) {
			jButtonExit = new JButton();
			jButtonExit.setBounds(new Rectangle(30, 405, 106, 31));
			jButtonExit.setText("Shutdown");
			jButtonExit.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					System.exit(0);
				}
			});
		}
		return jButtonExit;
	}

	/**
	 * This method initializes jButtonStart	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonStart() {
		if (jButtonStart == null) {
			jButtonStart = new JButton();
			jButtonStart.setBounds(new Rectangle(405, 360, 106, 31));
			jButtonStart.setText("Start");
			jButtonStart.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					startServer();
					
				}
			});
		}
		return jButtonStart;
	}

	/**
	 * This method initializes jButtonStop	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonStop() {
		if (jButtonStop == null) {
			jButtonStop = new JButton();
			jButtonStop.setBounds(new Rectangle(405, 405, 106, 31));
			jButtonStop.setEnabled(false);
			jButtonStop.setText("Stop");
			jButtonStop.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					stopServer();
					
				}
			});
		}
		return jButtonStop;
	}

	/**
	 * This method initializes jButtonLoadPrivateKey	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSettings() {
		if (jButtonSettings == null) {
			jButtonSettings = new JButton();
			jButtonSettings.setBounds(new Rectangle(150, 405, 106, 31));
			jButtonSettings.setText("Settings");
			jButtonSettings.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					(new TellerSettingsDialog(settings)).setVisible(true);
					
				}
			});
		}
		return jButtonSettings;
	}

	/**
	 * This method initializes jButtonIdentifyToBulletinBoard	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonIdentifyToBulletinBoard() {
		if (jButtonIdentifyToBulletinBoard == null) {
			jButtonIdentifyToBulletinBoard = new JButton();
			jButtonIdentifyToBulletinBoard.setBounds(new Rectangle(30, 360, 226, 31));
			jButtonIdentifyToBulletinBoard.setText("Identify to bulletin board");
			jButtonIdentifyToBulletinBoard.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					identifyToBulletinBoard();
					
				}
			});
		}
		return jButtonIdentifyToBulletinBoard;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		//Show a GUI
		(new TellerGUI()).setVisible(true);
	}

	/**
	 * This is the default constructor
	 */
	public TellerGUI() {
		super();
		initialize();
		
		try {

			//Load settings file
			Properties props = new Properties();
	        props.load(Class.class.getResourceAsStream("/uk/ac/surrey/pav/teller/teller.prop"));
	        
	        //Load individual settings
	        this.settings.setTellerName(props.getProperty("tellername"));
	        this.settings.setServerAddress(props.getProperty("serveraddress"));
	        this.settings.setServerName(props.getProperty("servername"));
	        this.settings.setDatabaseConnectionString(props.getProperty("dburl"));
	        this.settings.setDatabaseUserName(props.getProperty("dbusername"));
	        this.settings.setDatabasePassword(props.getProperty("dbpassword"));
	        this.settings.setBulletinBoardServerAddress(props.getProperty("wbbserveraddress"));
	        this.settings.setBulletinBoardServerName(props.getProperty("wbbservername"));
	        
		} catch (IOException e) {
			
			//Could not open properties file
			
		}

		try {

			//Load teller private key from file
			ObjectInputStream objectIn = new ObjectInputStream(Class.class.getResourceAsStream("/uk/ac/surrey/pav/teller/Teller_private_key.ppk"));
			this.settings.setPrivateKey((PrivateKey)objectIn.readObject());
			
		} catch (Exception e) {
			
			//Could not load key from file
			
		}

		try {

			//Load bulletin board public key from file
			ObjectInputStream objectIn = new ObjectInputStream(Class.class.getResourceAsStream("/uk/ac/surrey/pav/teller/BulletinBoard_public_key.ppk"));
			this.settings.setPublicKey((PublicKey)objectIn.readObject());
			
		} catch (Exception e) {
			
			//Could not load key from file
			
		}

	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(548, 497);
		this.setResizable(false);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Prêt à Voter Teller");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelTitle = new JLabel();
			jLabelTitle.setBounds(new java.awt.Rectangle(30,15,481,46));
			jLabelTitle.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelTitle.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelTitle.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 36));
			jLabelTitle.setText("Prêt à Voter Teller");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(getJScrollPaneTellerStatus(), null);
			jContentPane.add(getJButtonExit(), null);
			jContentPane.add(jLabelTitle, null);
			jContentPane.add(getJButtonStart(), null);
			jContentPane.add(getJButtonStop(), null);
			jContentPane.add(getJButtonSettings(), null);
			jContentPane.add(getJButtonIdentifyToBulletinBoard(), null);
		}
		return jContentPane;
	}
	
	/**
	 * Starts the server and binds it
	 *
	 */
	private void startServer() {
	
		//Connect to the database
		settings.connectToDatabase();
		
		if(settings.isProper()) {

			try {
			
				//Start a server
				server = new TellerServer(settings);
	
				//Bind the server
				Naming.rebind(settings.getServerName(), server);
				
				//Grey the button
				this.getJButtonStart().setEnabled(false);
				this.getJButtonStop().setEnabled(true);
				this.getJButtonSettings().setEnabled(false);
				
			} catch (Exception e1) {
	
				e1.printStackTrace();
				JOptionPane.showMessageDialog(this, e1.getMessage(), "Error", JOptionPane.ERROR_MESSAGE);
			
			}
			
		} else {

			JOptionPane.showMessageDialog(this, "Settings are incomplete.", "Error", JOptionPane.ERROR_MESSAGE);

		}

	}
	
	/**
	 * Stops the server and unbinds it
	 *
	 */
	private void stopServer() {
		
		try {

			//Unbind
			Naming.unbind(settings.getServerName());
			
			//Set the server status
			this.settings.setStatus(false, "Stopped");
			
			//Delete the server
			this.server = null;
			
			//Grey the button
			getJButtonStop().setEnabled(false);
			getJButtonStart().setEnabled(true);
			getJButtonSettings().setEnabled(true);

		} catch (Exception e1) {

			e1.printStackTrace();
			JOptionPane.showMessageDialog(this, "Unable to unbind the server.", "Error", JOptionPane.ERROR_MESSAGE);

		}
		
	}
	
	/**
	 * Connects to the web bulletin board over RMI and identifies
	 * as teller, giving details on its new address
	 *
	 */
	private void identifyToBulletinBoard() {
		
		try {

			//Check that there are appropriate settings
			if(this.settings.getServerAddress() != null
					&& this.settings.getServerName() != null
					&& this.settings.getBulletinBoardServerAddress() != null
					&& this.settings.getBulletinBoardServerName() != null) {
			
				//Connect to bulletin board
				BulletinBoardInterface bulletinBoard = (BulletinBoardInterface)Naming.lookup("rmi://" + this.settings.getBulletinBoardServerAddress() + "/" + this.settings.getBulletinBoardServerName());
				
				//Get nonce from bulletin board
				byte[] nonce = bulletinBoard.identifyTellerGetNonce(this.settings.getTellerName());
						
				//Check we got something from the wbb
				if(nonce != null)  {

					//Create hash of details
					Signature signature = Signature.getInstance("SHA1withRSA");
					signature.initSign(this.settings.getPrivateKey());
					
					//Add teller name to digest
					signature.update(this.settings.getTellerName().getBytes("ISO-8859-1"));
					
					//Add teller server name to digest
					signature.update(this.settings.getServerName().getBytes("ISO-8859-1"));

					//Add teller server address to digest
					signature.update(this.settings.getServerAddress().getBytes("ISO-8859-1"));

					//Add nonce to digest
					signature.update(nonce);
					
					//Identify to bulletin board
					if(bulletinBoard.identifyTeller(this.settings.getTellerName(), this.settings.getServerName(), this.settings.getServerAddress(), signature.sign())) {

						JOptionPane.showMessageDialog(this, "Successfully identified to the bulletin board.", "Error", JOptionPane.PLAIN_MESSAGE);

					} else {

						JOptionPane.showMessageDialog(this, "The bulletin board did not accept the identification.", "Error", JOptionPane.ERROR_MESSAGE);

					}

				} else {

					JOptionPane.showMessageDialog(this, "The bulletin board did not offer a nonce.", "Error", JOptionPane.ERROR_MESSAGE);

				}

				
			} else {

				JOptionPane.showMessageDialog(this, "Settings are missing, Teller and Bulletin board server details are needed.", "Error", JOptionPane.ERROR_MESSAGE);

			}

		} catch (RemoteException e) {

			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "Unable to connect to bulletin board! (RemoteException)", "Error", JOptionPane.ERROR_MESSAGE);

		} catch (NotBoundException e) {
			
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "Unable to connect to bulletin board! (NotBoundException)", "Error", JOptionPane.ERROR_MESSAGE);

		} catch (MalformedURLException e) {
			
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "The bulletin board URL is malformed: rmi://" + this.settings.getBulletinBoardServerAddress() + "/" + this.settings.getBulletinBoardServerName(), "Error", JOptionPane.ERROR_MESSAGE);
			
		} catch (NoSuchAlgorithmException e) {
			
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "Unable to create a SHA1 hash (NoSuchAlgorithmException)", "Error", JOptionPane.ERROR_MESSAGE);
			
		} catch (SignatureException e) {
			
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "Unable to create a SHA1 hash (SignatureException)", "Error", JOptionPane.ERROR_MESSAGE);
			
		} catch (UnsupportedEncodingException e) {
			
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "Unable to use ISO-8859-1 encoding.", "Error", JOptionPane.ERROR_MESSAGE);
			
		} catch (InvalidKeyException e) {
			
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "The teller privatee", "Error", JOptionPane.ERROR_MESSAGE);
			
		}
		
	}
	
}  //  @jve:decl-index=0:visual-constraint="10,10"
