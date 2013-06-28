package uk.ac.surrey.pav.auditmachine;

import java.rmi.ConnectException;
import java.rmi.Naming;
import java.security.Signature;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import uk.ac.surrey.pav.ballotform.Permutation;
import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;
import uk.ac.surrey.pav.common.ClientSettings;
import uk.ac.surrey.pav.common.Setup;

/**
 * A graphical audit machine
 * 
 * @author David Lundin
 *
 */
public class AuditMachine extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabelMainTitle = null;
	private JLabel jLabelEnterSerialNo = null;
	private JButton jButtonOK = null;
	private JTextField jTextFieldSerialNo = null;
	
	/**
	 * Settings for the audit machine
	 */
	private ClientSettings settings;

	private JButton jButtonSetup = null;

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new java.awt.Rectangle(195,195,211,46));
			jButtonOK.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 24));
			jButtonOK.setText("AUDIT FORM");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					if(getJTextFieldSerialNumber().getText().length() > 0) {
						int ballotID = Integer.parseInt(getJTextFieldSerialNumber().getText());
						audit(ballotID);
					}
				}
			});
		}
		return jButtonOK;
	}

	/**
	 * This method initializes jTextFieldSerialNumber	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldSerialNumber() {
		if (jTextFieldSerialNo == null) {
			jTextFieldSerialNo = new JTextField();
			jTextFieldSerialNo.setBounds(new java.awt.Rectangle(135,135,331,46));
			jTextFieldSerialNo.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 24));
		}
		return jTextFieldSerialNo;
	}

	/**
	 * This method initializes jButtonSetup	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSetup() {
		if (jButtonSetup == null) {
			jButtonSetup = new JButton();
			jButtonSetup.setBounds(new java.awt.Rectangle(15,15,76,31));
			jButtonSetup.setText("Setup");
			jButtonSetup.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					(new Setup(settings)).setVisible(true);
				}
			});
		}
		return jButtonSetup;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		(new AuditMachine()).setVisible(true);
		
	}

	/**
	 * This is the default constructor
	 */
	public AuditMachine() {
		super();
		this.settings = new ClientSettings();
		initialize();
		(new Setup(settings)).setVisible(true);
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(854, 537);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Audit Machine");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelEnterSerialNo = new JLabel();
			jLabelEnterSerialNo.setBounds(new java.awt.Rectangle(135,75,331,46));
			jLabelEnterSerialNo.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 24));
			jLabelEnterSerialNo.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelEnterSerialNo.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelEnterSerialNo.setText("ENTER SERIAL NUMBER:");
			jLabelMainTitle = new JLabel();
			jLabelMainTitle.setBounds(new java.awt.Rectangle(15,15,676,46));
			jLabelMainTitle.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 48));
			jLabelMainTitle.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelMainTitle.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelMainTitle.setText("AUDIT YOUR BALLOT FORM");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelMainTitle, null);
			jContentPane.add(jLabelEnterSerialNo, null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.add(getJTextFieldSerialNumber(), null);
			jContentPane.add(getJButtonSetup(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					//Vars
					int centre = jContentPane.getWidth() / 2;
					int margin = 30;
					
					//Move the texts etc
					jLabelMainTitle.setLocation(centre - jLabelMainTitle.getWidth() / 2, (jContentPane.getHeight() - jLabelMainTitle.getHeight() - jLabelEnterSerialNo.getHeight() - getJTextFieldSerialNumber().getHeight() - getJButtonOK().getHeight() - (3 * margin)) / 2);
					jLabelEnterSerialNo.setLocation(centre - jLabelEnterSerialNo.getWidth() / 2, jLabelMainTitle.getLocation().y + jLabelMainTitle.getHeight() + margin);
					getJTextFieldSerialNumber().setLocation(centre - getJTextFieldSerialNumber().getWidth() / 2, jLabelEnterSerialNo.getLocation().y + jLabelEnterSerialNo.getHeight() + margin);
					getJButtonOK().setLocation(centre - getJButtonOK().getWidth() / 2, getJTextFieldSerialNumber().getLocation().y + getJTextFieldSerialNumber().getHeight() + margin);

				}
				public void componentMoved(java.awt.event.ComponentEvent e) {
				}
				public void componentShown(java.awt.event.ComponentEvent e) {
				}
				public void componentHidden(java.awt.event.ComponentEvent e) {
				}
			});
		}
		return jContentPane;
	}
	
	/**
	 * Send off an audit request
	 * 
	 * @param ballotID ID of the ballot form to audit
	 */
	private void audit(int serialNo) {
		
		try {

			//Connect to the bulletin board
			BulletinBoardInterface remoteBulletinBoard = (BulletinBoardInterface)Naming.lookup("rmi://" + this.settings.bulletinBoardAddress + "/" + this.settings.bulletinBoardName);
				
			//Create the signature object
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initSign(settings.privateKey);
		
			//Add the ballot form serial number
			signature.update((serialNo + "").getBytes());
	
			//Invoke the remote method
			String[] resultPermutation = remoteBulletinBoard.auditForm(serialNo, settings.ID, signature.sign());
				
			//Show the result
			JOptionPane.showMessageDialog(this, resultPermutation, "Result", JOptionPane.INFORMATION_MESSAGE);

			
		} catch (ConnectException ex) {

			JOptionPane.showMessageDialog(this, "Unable to connect to the web bulletin board.", "Error", JOptionPane.ERROR_MESSAGE);

		} catch (Exception ex) {

			ex.printStackTrace();
			JOptionPane.showMessageDialog(this, ex.getMessage(), ex.toString(), JOptionPane.ERROR_MESSAGE);

		}

	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
