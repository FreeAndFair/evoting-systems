package uk.ac.surrey.pav.bulletinboard.batches;

import javax.swing.JPanel;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JProgressBar;

/**
 * Dialog that shows the progress of the creation of and sending
 * and receiving of batches. 
 * 
 * @author David Lundin
 *
 */
public class BatchCreatorDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabelTitle = null;
	private JProgressBar jProgressBar = null;
	
	/**
	 * The thread doing the creating
	 */
	private BatchCreator creator;
	
	/**
	 * The thread doing the updating of the progress bar
	 */
	private BatchCreatorUpdatorThread thread;

	/**
	 * This is the default constructor
	 */
	public BatchCreatorDialog(BatchCreator creator) {
		super();
		initialize();
		
		//Store the creator running in a different thread
		this.creator = creator;
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(455, 167);
		this.setTitle("Creating batch...");
		this.setModal(false);
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
			jLabelTitle = new JLabel();
			jLabelTitle.setBounds(new java.awt.Rectangle(30,30,391,31));
			jLabelTitle.setText("Creating batch... PLEASE WAIT");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelTitle, null);
			jContentPane.add(getJProgressBar(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jProgressBar	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBar() {
		if (jProgressBar == null) {
			jProgressBar = new JProgressBar();
			jProgressBar.setBounds(new java.awt.Rectangle(30,75,391,31));
			jProgressBar.setStringPainted(true);
		}
		return jProgressBar;
	}
	
	/**
	 * Returns reference to the progress bar for the thread that updates it
	 * 
	 * @return JProgressBar
	 */
	public JProgressBar getProgressBar() {
		return this.getJProgressBar();
	}
	
	/**
	 * Returns reference to the label into which to set out the current status
	 * 
	 * @return JLabel
	 */
	public JLabel getProgressLabel() {
		return this.jLabelTitle;
	}

}  //  @jve:decl-index=0:visual-constraint="2,7"
