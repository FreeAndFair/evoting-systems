package org.scantegrity.erm;

import java.awt.GridBagLayout;
import javax.swing.JPanel;
import java.awt.Dimension;
import javax.swing.JLabel;
import java.awt.GridBagConstraints;
import java.awt.Insets;

public class StatisticsPanel extends JPanel {

	private static final long serialVersionUID = 1L;
	private JLabel ballotCountLabel = null;
	private JLabel ballotCount = null;
	private JLabel writeInCountLabel = null;
	private JLabel writeInCount = null;
	private JLabel errorCountLabel = null;
	private JLabel errorCount = null;

	/**
	 * This is the default constructor
	 */
	public StatisticsPanel() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		GridBagConstraints gridBagConstraints5 = new GridBagConstraints();
		gridBagConstraints5.gridx = 6;
		gridBagConstraints5.gridy = 0;
		errorCount = new JLabel();
		errorCount.setText("0");
		GridBagConstraints gridBagConstraints4 = new GridBagConstraints();
		gridBagConstraints4.gridx = 5;
		gridBagConstraints4.ipadx = 10;
		gridBagConstraints4.anchor = GridBagConstraints.EAST;
		gridBagConstraints4.insets = new Insets(0, 20, 0, 0);
		gridBagConstraints4.gridy = 0;
		errorCountLabel = new JLabel();
		errorCountLabel.setText("Error Contests:");
		GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
		gridBagConstraints3.gridx = 4;
		gridBagConstraints3.gridy = 0;
		writeInCount = new JLabel();
		writeInCount.setText("0");
		GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
		gridBagConstraints2.gridx = 3;
		gridBagConstraints2.ipadx = 10;
		gridBagConstraints2.anchor = GridBagConstraints.EAST;
		gridBagConstraints2.insets = new Insets(0, 20, 0, 0);
		gridBagConstraints2.gridy = 0;
		writeInCountLabel = new JLabel();
		writeInCountLabel.setText("WriteIns:");
		GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
		gridBagConstraints1.gridx = 2;
		gridBagConstraints1.gridy = 0;
		ballotCount = new JLabel();
		ballotCount.setText("0");
		GridBagConstraints gridBagConstraints = new GridBagConstraints();
		gridBagConstraints.gridx = 0;
		gridBagConstraints.ipadx = 10;
		gridBagConstraints.gridy = 0;
		ballotCountLabel = new JLabel();
		ballotCountLabel.setText("Valid Ballots:");
		this.setSize(500, 300);
		this.setLayout(new GridBagLayout());
		this.add(ballotCountLabel, gridBagConstraints);
		this.add(ballotCount, gridBagConstraints1);
		this.add(writeInCountLabel, gridBagConstraints2);
		this.add(writeInCount, gridBagConstraints3);
		this.add(errorCountLabel, gridBagConstraints4);
		this.add(errorCount, gridBagConstraints5);
	}
	
	public void addBallotCount(int p_count)
	{
		ballotCount.setText(Integer.toString(Integer.parseInt(ballotCount.getText()) + p_count));
	}
	
	public void removeBallotCount(int p_count)
	{
		ballotCount.setText(Integer.toString(Integer.parseInt(ballotCount.getText()) - p_count));
	}
	
	public void setWriteInCount(int p_count)
	{
		writeInCount.setText(Integer.toString(p_count));
	}
	
	public void setErrorCount(int p_count) {
		errorCount.setText(Integer.toString(p_count));
	}

}  //  @jve:decl-index=0:visual-constraint="0,0"
