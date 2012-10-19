package org.scantegrity.erm;

import java.awt.BorderLayout;
import java.awt.Frame;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.util.Vector;

import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import org.scantegrity.common.RandomBallotStore;

public class BallotStoreDialog extends JDialog {

	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	public Vector<RandomBallotStore> c_stores = null;
	private JLabel headerLabel = null;
	private JScrollPane jScrollPane = null;
	private JList jList = null;
	private JPanel buttonPanel = null;
	private JButton yesButton = null;
	private JButton noButton = null;
	private DefaultListModel c_model = null;

	/**
	 * @param owner
	 */
	public BallotStoreDialog(Frame owner, Vector<RandomBallotStore> p_stores) {
		super(owner, true);
		setTitle("Confirm");
		c_stores = p_stores;
		c_model = new DefaultListModel();
		for( RandomBallotStore p_store : p_stores )
		{
			c_model.addElement(p_store.getScannerId());
		}
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
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			headerLabel = new JLabel();
			headerLabel.setText("<HTML>Would you like to add the ballot stores from these scanners?</HTML>");
			jContentPane = new JPanel();
			jContentPane.setLayout(new BorderLayout());
			jContentPane.add(headerLabel, BorderLayout.NORTH);
			jContentPane.add(getJScrollPane(), BorderLayout.CENTER);
			jContentPane.add(getButtonPanel(), BorderLayout.SOUTH);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPane() {
		if (jScrollPane == null) {
			jScrollPane = new JScrollPane();
			jScrollPane.setViewportView(getJList());
		}
		return jScrollPane;
	}

	/**
	 * This method initializes jList	
	 * 	
	 * @return javax.swing.JList	
	 */
	private JList getJList() {
		if (jList == null) {
			jList = new JList();
			jList.setModel(c_model);
		}
		return jList;
	}

	/**
	 * This method initializes buttonPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getButtonPanel() {
		if (buttonPanel == null) {
			buttonPanel = new JPanel();
			buttonPanel.setLayout(new GridBagLayout());
			GridBagConstraints l_c1 = new GridBagConstraints();
			GridBagConstraints l_c2 = new GridBagConstraints();
			l_c1.gridx = 0;
			l_c1.gridy = 0;
			l_c1.weightx = .5;
			l_c2.gridx = 1;
			l_c2.gridy = 0;
			l_c2.weightx = .5;
			
			buttonPanel.add(getYesButton(), l_c1);
			buttonPanel.add(getNoButton(), l_c2);
		}
		return buttonPanel;
	}

	/**
	 * This method initializes yesButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getYesButton() {
		if (yesButton == null) {
			yesButton = new JButton();
			yesButton.setText("Yes");
			yesButton.addActionListener(new java.awt.event.ActionListener() {   
				public void actionPerformed(java.awt.event.ActionEvent e) {    
					setVisible(false);
				}
			
			});
		}
		return yesButton;
	}

	/**
	 * This method initializes noButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getNoButton() {
		if (noButton == null) {
			noButton = new JButton();
			noButton.setText("No");
			noButton.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					c_stores.clear();
					setVisible(false);
				}
			});
		}
		return noButton;
	}

}
