package uk.ac.surrey.pav.bulletinboard;

import javax.swing.JPanel;
import javax.swing.JFrame;
import javax.swing.JCheckBox;
import javax.swing.JButton;

/**
 * Allows the settings for the dash board to be changed
 * 
 * @author David Lundin
 *
 */
public class DashboardSettingsDialog extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	private JCheckBox jCheckBoxDisplayBallotForms = null;
	
	/**
	 * Settings that this dashboard changes
	 */
	private DashboardSettings settings;
	private JButton jButtonOK = null;

	/**
	 * This is the default constructor
	 */
	public DashboardSettingsDialog(DashboardSettings settings) {
		super();
		
		/*
		 * Store reference to settings
		 */
		this.settings = settings;
		
		/*
		 * Initialise
		 */
		initialize();

	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(486, 263);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setResizable(false);
		this.setContentPane(getJContentPane());
		this.setTitle("Settings");
		
		/*
		 * Set the correct options
		 */
		
		if(this.settings.isShowBallotFormsOnSubmission()) {
			//getJCheckBoxDisplayBallotForms().
		}
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
			jContentPane.add(getJCheckBoxDisplayBallotForms(), null);
			jContentPane.add(getJButtonOK(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jCheckBoxDisplayBallotForms	
	 * 	
	 * @return javax.swing.JCheckBox	
	 */
	private JCheckBox getJCheckBoxDisplayBallotForms() {
		if (jCheckBoxDisplayBallotForms == null) {
			jCheckBoxDisplayBallotForms = new JCheckBox();
			jCheckBoxDisplayBallotForms.setBounds(new java.awt.Rectangle(15,15,451,31));
			jCheckBoxDisplayBallotForms.setText("Display ballot forms as they are received");
		}
		return jCheckBoxDisplayBallotForms;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new java.awt.Rectangle(195,180,106,31));
			jButtonOK.setText("OK");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					close();
					
				}
			});
		}
		return jButtonOK;
	}
	
	private void close() {
		//Store the values
		
		//Close the window
		this.setVisible(false);
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
