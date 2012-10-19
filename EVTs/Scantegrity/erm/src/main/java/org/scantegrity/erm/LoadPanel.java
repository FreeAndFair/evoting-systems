package org.scantegrity.erm;

import java.awt.BorderLayout;
import java.io.File;

import javax.swing.JLabel;
import javax.swing.JPanel;

public class LoadPanel extends JPanel {

	private static final long serialVersionUID = 1L;
	private WriteInResolver c_resolver = null;
	private ErrorBallotResolver c_errorResolver = null;
	private JLabel headerLabel = null;
	private String c_path = null;
	private BallotStorePanel ballotStorePanel = null;
	private StatisticsPanel statisticsPanel = null;
	/**
	 * This is the default constructor
	 * @param c_errorResolver 
	 */
	public LoadPanel(WriteInResolver p_resolver, ErrorBallotResolver p_errorResolver, String p_destFolder) {
		super();
		c_resolver = p_resolver;
		c_errorResolver = p_errorResolver; 
		c_path = p_destFolder;
		File l_file = new File(c_path);
		if( !l_file.exists() )
			l_file.mkdir();
		
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		headerLabel = new JLabel();
		headerLabel.setText("Please insert memory cards from each machine, one at a time, and click the 'scan' button.");
		this.setSize(600, 400);
		this.setLayout(new BorderLayout());
		this.add(headerLabel, BorderLayout.NORTH);
		this.add(getBallotStorePanel(), BorderLayout.CENTER);
		this.add(getStatisticsPanel(), BorderLayout.SOUTH);
	}

	/**
	 * This method initializes ballotStorePanel	
	 * 	
	 * @return org.scantegrity.erm.BallotStorePanel	
	 */
	private BallotStorePanel getBallotStorePanel() {
		if (ballotStorePanel == null) {
			ballotStorePanel = new BallotStorePanel(c_resolver, c_errorResolver, c_path, getStatisticsPanel());
		}
		return ballotStorePanel;
	}

	/**
	 * This method initializes statisticsPanel	
	 * 	
	 * @return org.scantegrity.erm.StatisticsPanel	
	 */
	private StatisticsPanel getStatisticsPanel() {
		if (statisticsPanel == null) {
			statisticsPanel = new StatisticsPanel();
		}
		return statisticsPanel;
	}

}
