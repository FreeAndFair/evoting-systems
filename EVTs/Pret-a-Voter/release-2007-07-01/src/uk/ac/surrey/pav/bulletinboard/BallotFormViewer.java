package uk.ac.surrey.pav.bulletinboard;

import java.awt.BorderLayout;
import javax.swing.JPanel;
import javax.swing.JFrame;

public class BallotFormViewer extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;

	/**
	 * This is the default constructor
	 */
	public BallotFormViewer() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(300, 200);
		this.setContentPane(getJContentPane());
		this.setTitle("Ballot form viewer");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jContentPane = new JPanel();
			jContentPane.setLayout(new BorderLayout());
		}
		return jContentPane;
	}

}
