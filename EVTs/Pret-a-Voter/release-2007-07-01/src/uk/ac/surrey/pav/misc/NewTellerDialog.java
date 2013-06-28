package uk.ac.surrey.pav.misc;

import javax.swing.JPanel;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JTextField;

public class NewTellerDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabel = null;
	private JTextField jTextField = null;

	/**
	 * This is the default constructor
	 */
	public NewTellerDialog() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(445, 319);
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabel = new JLabel();
			jLabel.setText("Name:");
			jLabel.setBounds(new java.awt.Rectangle(15,15,76,16));
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabel, null);
			jContentPane.add(getJTextField(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jTextField	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextField() {
		if (jTextField == null) {
			jTextField = new JTextField();
			jTextField.setBounds(new java.awt.Rectangle(106,16,240,30));
		}
		return jTextField;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
