package uk.ac.surrey.pav.bulletinboard.challenges;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.tablemodels.ChallengeTableModel;
import javax.swing.JButton;
import javax.swing.JProgressBar;

/**
 * GUI that displays the progress as the tellers are challenged
 * 
 * @author David Lundin
 *
 */
public class ChallengeDialog extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	private JScrollPane jScrollPaneChallenges = null;
	private JTable jTableChallenges = null;

	/**
	 * The race that we are here concerned with
	 */
	private Race race;
	
	/**
	 * A bulletin board that holds all settings and connections
	 */
	private BulletinBoard bulletinBoard;
	
	private JButton jButtonGetCommitments = null;
	private JButton jButtonClose = null;
	
	private Challenger challenger;
	private Thread challengerThread;
	private JProgressBar jProgressBarTotal = null;
	private JProgressBar jProgressBarCurrent = null;
	
	/**
	 * This is the default constructor
	 */
	public ChallengeDialog(BulletinBoard bulletinBoard, Race race) {
		super();
		
		//Store references
		this.bulletinBoard = bulletinBoard;
		this.race = race;

		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(666, 335);
		this.setResizable(false);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Challenges");
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
			jContentPane.add(getJScrollPaneChallenges(), null);
			jContentPane.add(getJButtonGetCommitments(), null);
			jContentPane.add(getJButtonClose(), null);
			jContentPane.add(getJProgressBarTotal(), null);
			jContentPane.add(getJProgressBarCurrent(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					/*A margin
					int margin = 15;
					
					//Table
					getJScrollPaneChallenges().setSize(getJContentPane().getWidth() - (2 * margin), getJContentPane().getHeight() - getJButtonGetCommitments().getHeight() - (3 * margin));
					getJScrollPaneChallenges().setLocation(margin, margin);
					
					//Buttons
					getJButtonGetCommitments().setLocation(margin, getJContentPane().getHeight() - getJButtonGetCommitments().getHeight() - margin);
					getJButtonGetValues().setLocation(getJButtonGetCommitments().getLocation().x + getJButtonGetCommitments().getWidth() + margin, getJButtonGetCommitments().getLocation().y);
					getJButtonClose().setLocation(getJContentPane().getWidth() - getJButtonClose().getWidth() - margin, getJButtonGetCommitments().getLocation().y);	*/
					
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
	 * This method initializes jScrollPaneChallenges	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneChallenges() {
		if (jScrollPaneChallenges == null) {
			jScrollPaneChallenges = new JScrollPane();
			jScrollPaneChallenges.setBounds(new java.awt.Rectangle(15,15,631,136));
			jScrollPaneChallenges.setViewportView(getJTableChallenges());
		}
		return jScrollPaneChallenges;
	}

	/**
	 * This method initializes jTableChallenges	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableChallenges() {
		if (jTableChallenges == null) {
			jTableChallenges = new JTable(new ChallengeTableModel(bulletinBoard, race));
			jTableChallenges.setBounds(new java.awt.Rectangle(45,15,631,346));
		}
		return jTableChallenges;
	}

	/**
	 * This method initializes jButtonGetCommitments	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonGetCommitments() {
		if (jButtonGetCommitments == null) {
			jButtonGetCommitments = new JButton();
			jButtonGetCommitments.setBounds(new java.awt.Rectangle(15,255,151,31));
			jButtonGetCommitments.setText("Start");
			jButtonGetCommitments.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					toggleChallenger();
					
				}
			});
		}
		return jButtonGetCommitments;
	}

	/**
	 * This method initializes jButtonClose	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonClose() {
		if (jButtonClose == null) {
			jButtonClose = new JButton();
			jButtonClose.setBounds(new java.awt.Rectangle(495,255,151,31));
			jButtonClose.setText("Close");
			jButtonClose.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					close();
					
				}
			});
		}
		return jButtonClose;
	}

	/**
	 * Closes the window
	 *
	 */
	private void close() {
		
		this.setVisible(false);
		
	}
	
	/**
	 * Starts or stops the challenger thread
	 *
	 */
	private void toggleChallenger() {
		
		this.challenger = new Challenger(this.bulletinBoard, this.race, this.getJProgressBarTotal(), this.getJProgressBarCurrent());
		this.challengerThread = new Thread(challenger);
		this.challengerThread.start();

	}

	/**
	 * This method initializes jProgressBarChallenges	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBarTotal() {
		if (jProgressBarTotal == null) {
			jProgressBarTotal = new JProgressBar();
			jProgressBarTotal.setBounds(new java.awt.Rectangle(15,210,631,31));
			jProgressBarTotal.setString("(Not started)");
			jProgressBarTotal.setStringPainted(true);
		}
		return jProgressBarTotal;
	}

	/**
	 * This method initializes jProgressBarCurrent	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBarCurrent() {
		if (jProgressBarCurrent == null) {
			jProgressBarCurrent = new JProgressBar();
			jProgressBarCurrent.setBounds(new java.awt.Rectangle(15,165,631,31));
			jProgressBarCurrent.setStringPainted(true);
			jProgressBarCurrent.setString("(Not started)");
		}
		return jProgressBarCurrent;
	}
	
}  //  @jve:decl-index=0:visual-constraint="10,10"
