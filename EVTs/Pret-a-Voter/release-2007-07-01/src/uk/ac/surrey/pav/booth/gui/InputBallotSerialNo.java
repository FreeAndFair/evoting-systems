package uk.ac.surrey.pav.booth.gui;

import java.awt.BorderLayout;
import javax.swing.JPanel;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.JButton;

/**
 * A dialog box to accept a ballot form serial number
 * 
 * @author David Lundin
 *
 */
public class InputBallotSerialNo extends JDialog {

	private JPanel jContentPane = null;
	private JLabel jLabelEnterSerialNo = null;
	private JTextField jTextFieldSerialNo = null;
	private JButton jButtonOK = null;

	/**
	 * This method initializes jTextFieldSerialNo	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldSerialNo() {
		if (jTextFieldSerialNo == null) {
			jTextFieldSerialNo = new JTextField();
			jTextFieldSerialNo.setBounds(new java.awt.Rectangle(135,90,241,46));
			jTextFieldSerialNo.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 24));
		}
		return jTextFieldSerialNo;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new java.awt.Rectangle(195,150,121,46));
			jButtonOK.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 24));
			jButtonOK.setText("OK");
		}
		return jButtonOK;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

	/**
	 * This is the default constructor
	 */
	public InputBallotSerialNo() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(515, 260);
		this.setTitle("Please enter ballot form serial number");
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelEnterSerialNo = new JLabel();
			jLabelEnterSerialNo.setBounds(new java.awt.Rectangle(30,30,451,46));
			jLabelEnterSerialNo.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelEnterSerialNo.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelEnterSerialNo.setFont(new java.awt.Font("Dialog", java.awt.Font.PLAIN, 24));
			jLabelEnterSerialNo.setText("Please enter ballot form serial number:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelEnterSerialNo, null);
			jContentPane.add(getJTextFieldSerialNo(), null);
			jContentPane.add(getJButtonOK(), null);
		}
		return jContentPane;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
