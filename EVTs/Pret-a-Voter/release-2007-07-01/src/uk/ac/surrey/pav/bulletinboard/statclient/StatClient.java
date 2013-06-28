package uk.ac.surrey.pav.bulletinboard.statclient;

import javax.swing.JPanel;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTabbedPane;

public class StatClient extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	private JScrollPane jScrollPaneStats = null;
	private JTable jTableStats = null;
	private JTabbedPane jTabbedPaneStats = null;

	/**
	 * This method initializes jScrollPaneStats	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneStats() {
		if (jScrollPaneStats == null) {
			jScrollPaneStats = new JScrollPane();
			jScrollPaneStats.setBounds(new java.awt.Rectangle(15,15,226,436));
			jScrollPaneStats.setViewportView(getJTableStats());
		}
		return jScrollPaneStats;
	}

	/**
	 * This method initializes jTableStats	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableStats() {
		if (jTableStats == null) {
			jTableStats = new JTable();
		}
		return jTableStats;
	}

	/**
	 * This method initializes jTabbedPaneStats	
	 * 	
	 * @return javax.swing.JTabbedPane	
	 */
	private JTabbedPane getJTabbedPaneStats() {
		if (jTabbedPaneStats == null) {
			jTabbedPaneStats = new JTabbedPane();
			jTabbedPaneStats.setBounds(new java.awt.Rectangle(255,15,451,436));
		}
		return jTabbedPaneStats;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {

		(new StatClient()).setVisible(true);
		
	}

	/**
	 * This is the default constructor
	 */
	public StatClient() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(733, 530);
		this.setDefaultCloseOperation(javax.swing.JFrame.EXIT_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Prêt à Voter StatClient");
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
			jContentPane.add(getJScrollPaneStats(), null);
			jContentPane.add(getJTabbedPaneStats(), null);
		}
		return jContentPane;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
