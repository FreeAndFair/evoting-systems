package uk.ac.surrey.pav.misc;

import javax.swing.JPanel;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JButton;
import javax.swing.JProgressBar;
import javax.swing.JTable;

/**
 * NOT FINISHED NOT FINISHED NOT FINISHED NOT FINISHED
 * 
 * @author David Lundin
 *
 */
public class RunElection extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabelElectionInProgress = null;
	private JButton jButtonCloseElection = null;
	private JProgressBar jProgressBarElection = null;
	private JTable jTableStatus = null;
	
	/**
	 * The bulletin board server
	 */
	public Thread bulletinBoardThread;

	/**
	 * This is the default constructor
	 */
	public RunElection(Thread bulletinBoardThread) {
		super();
		initialize();
		
		//Store the bulletin board
		this.bulletinBoardThread = bulletinBoardThread;
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(447, 284);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setResizable(false);
		this.setContentPane(getJContentPane());
		this.setTitle("Progress");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelElectionInProgress = new JLabel();
			jLabelElectionInProgress.setBounds(new java.awt.Rectangle(15,15,406,31));
			jLabelElectionInProgress.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelElectionInProgress.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelElectionInProgress.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 24));
			jLabelElectionInProgress.setText("ELECTION IN PROGRESS");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelElectionInProgress, null);
			jContentPane.add(getJButtonCloseElection(), null);
			jContentPane.add(getJProgressBarElection(), null);
			jContentPane.add(getJTableStatus(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jButtonCloseElection	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCloseElection() {
		if (jButtonCloseElection == null) {
			jButtonCloseElection = new JButton();
			jButtonCloseElection.setBounds(new java.awt.Rectangle(263,192,159,35));
			jButtonCloseElection.setText("End Election");
		}
		return jButtonCloseElection;
	}

	/**
	 * This method initializes jProgressBarElection	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBarElection() {
		if (jProgressBarElection == null) {
			jProgressBarElection = new JProgressBar();
			jProgressBarElection.setBounds(new java.awt.Rectangle(13,151,408,29));
		}
		return jProgressBarElection;
	}

	/**
	 * This method initializes jTableStatus	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableStatus() {
		if (jTableStatus == null) {
			jTableStatus = new JTable();
			jTableStatus.setBounds(new java.awt.Rectangle(16,60,404,84));
		}
		return jTableStatus;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
