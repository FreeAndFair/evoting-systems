package uk.ac.surrey.pav.booth.gui;

import java.awt.BorderLayout;
import javax.swing.JPanel;
import javax.swing.JFrame;

import uk.ac.surrey.pav.auditmachine.AuditMachine;
import uk.ac.surrey.pav.common.ClientSettings;
import uk.ac.surrey.pav.common.Setup;

/**
 * Graphical interface for the voting booth
 * 
 * @author David Lundin
 *
 */
public class BoothGUI extends JFrame {

	private JPanel jContentPane = null;

	/**
	 * Settings for the booth
	 */
	private ClientSettings settings;

	/**
	 * @param args
	 */
	public static void main(String[] args) {

		(new BoothGUI()).setVisible(true);

	}

	/**
	 * This is the default constructor
	 */
	public BoothGUI() {
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
		this.setSize(843, 581);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Cast a ballot");
		this.setVisible(true);
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
		}
		return jContentPane;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
