package uk.ac.surrey.pav.administrator.registry;


import java.awt.Font;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.rmi.Naming;
import java.util.Properties;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.WindowConstants;

import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;

/**
 * A GUI that allows the user to search for a voter
 * 
 * @author David Lundin
 *
 */
public class SearchForVoter extends JFrame {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;
	
	private JLabel jLabelURN = null;

	private JTextField jTextFieldURN = null;

	private JButton jButtonSearch = null;
	
	/**
	 * The bulletin board server that we connect to
	 */
	private BulletinBoardInterface remoteBulletinBoard = null;

	private JLabel jLabelTitle = null;

	private JPanel jPanelScan = null;

	private JLabel jLabelScanOutput = null;

	private JButton jButtonScan = null;
	
	/**
	 * The external command to run to initiate a scan
	 */
	private String externalScanCommand;

	/**
	 * This method initializes jTextFieldURN	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldURN() {
		if (jTextFieldURN == null) {
			jTextFieldURN = new JTextField();
			jTextFieldURN.setBounds(new java.awt.Rectangle(300,105,226,46));
			jTextFieldURN.setFont(new Font("Dialog", Font.PLAIN, 24));
			jTextFieldURN.addKeyListener(new java.awt.event.KeyAdapter() {
				public void keyTyped(java.awt.event.KeyEvent e) {
					
					if(e.getKeyChar() == '\n') {
						search();
					}
					
				}
			});
		}
		return jTextFieldURN;
	}

	/**
	 * This method initializes jButtonSearch	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSearch() {
		if (jButtonSearch == null) {
			jButtonSearch = new JButton();
			jButtonSearch.setBounds(new java.awt.Rectangle(540,105,121,46));
			jButtonSearch.setFont(new Font("Dialog", Font.PLAIN, 18));
			jButtonSearch.setText("Search");
			jButtonSearch.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					search();
					
				}
			});
		}
		return jButtonSearch;
	}

	/**
	 * This method initializes jPanelScan	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getJPanelScan() {
		if (jPanelScan == null) {
			jLabelScanOutput = new JLabel();
			jLabelScanOutput.setText("(Scan process output)");
			jLabelScanOutput.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelScanOutput.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelScanOutput.setBounds(new java.awt.Rectangle(0,0,421,136));
			jPanelScan = new JPanel();
			jPanelScan.setLayout(null);
			jPanelScan.setBounds(new java.awt.Rectangle(225,240,421,211));
			jPanelScan.setBorder(javax.swing.BorderFactory.createBevelBorder(javax.swing.border.BevelBorder.LOWERED));
			jPanelScan.add(jLabelScanOutput, null);
			jPanelScan.add(getJButtonScan(), null);
		}
		return jPanelScan;
	}

	/**
	 * This method initializes jButtonScan	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonScan() {
		if (jButtonScan == null) {
			jButtonScan = new JButton();
			jButtonScan.setBounds(new java.awt.Rectangle(15,150,391,46));
			jButtonScan.setFont(new java.awt.Font("Dialog", java.awt.Font.BOLD, 24));
			jButtonScan.setMnemonic(java.awt.event.KeyEvent.VK_S);
			jButtonScan.setText("Scan");
			jButtonScan.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					scan();
					
				}
			});
		}
		return jButtonScan;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				SearchForVoter thisClass = new SearchForVoter();
				thisClass.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
				thisClass.setVisible(true);
			}
		});
	}

	/**
	 * This is the default constructor
	 */
	public SearchForVoter() {
		super();
		initialize();
		
        try {

			//Welcome message, ask for password
			/*String password = JOptionPane.showInputDialog("Welcome to the USSU Sabbatical Elections 2007.\nPlease enter the password:");
			
			if(password.compareTo("ussu2007pollpoll") != 0) {
				JOptionPane.showMessageDialog(this, "Incorrect password.", "Password", JOptionPane.ERROR_MESSAGE);
				System.exit(0);
			}*/

    		//Load settings
    		Properties props = new Properties();
			props.load(Class.class.getResourceAsStream("/uk/ac/surrey/pav/administrator/registry/registry.prop"));

			//The ID of the entity
			//int registryID = Integer.parseInt(props.getProperty("id"));
			
			//The external command to run to scan
			this.externalScanCommand = props.getProperty("scancommand");

			//The name of the election
			jLabelTitle.setText(props.getProperty("electionname"));

			//Connect to the web bulletin board
			this.remoteBulletinBoard = (BulletinBoardInterface)Naming.lookup("rmi://" + props.getProperty("wbburl") + "/" + props.getProperty("wbbname"));

        } catch (Exception e) {
        	
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "There was an error connecting to the database. Please restart application. (" + e.getMessage() + ")", "Connection error", JOptionPane.ERROR_MESSAGE);
			System.exit(1);

		}
        

	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(852, 564);
		this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Search for voter...");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelTitle = new JLabel();
			jLabelTitle.setBounds(new java.awt.Rectangle(15,15,811,76));
			jLabelTitle.setHorizontalAlignment(SwingConstants.CENTER);
			jLabelTitle.setHorizontalTextPosition(SwingConstants.CENTER);
			jLabelTitle.setFont(new Font("Dialog", Font.BOLD, 48));
			jLabelTitle.setText("(election name)");
			jLabelURN = new JLabel();
			jLabelURN.setBounds(new java.awt.Rectangle(180,105,106,45));
			jLabelURN.setFont(new Font("Dialog", Font.BOLD, 36));
			jLabelURN.setHorizontalAlignment(SwingConstants.RIGHT);
			jLabelURN.setHorizontalTextPosition(SwingConstants.RIGHT);
			jLabelURN.setText("URN:");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelURN, null);
			jContentPane.add(getJTextFieldURN(), null);
			jContentPane.add(getJButtonSearch(), null);
			jContentPane.add(jLabelTitle, null);
			jContentPane.add(getJPanelScan(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {
					
					//Set out the components nicely on the screen
					int margin = 15;
					int centre = jContentPane.getWidth() / 2;
					jLabelTitle.setLocation(centre - (jLabelTitle.getWidth() / 2), jContentPane.getHeight() / 3);

					int clusterWidth = jLabelURN.getWidth() + margin + getJTextFieldURN().getWidth() + margin + getJButtonSearch().getWidth();
					int clusterTop = jLabelTitle.getLocation().y + jLabelTitle.getHeight() + margin;
					
					jLabelURN.setLocation(centre - (clusterWidth / 2), clusterTop);
					jTextFieldURN.setLocation(jLabelURN.getLocation().x + jLabelURN.getWidth() + margin, clusterTop);
					getJButtonSearch().setLocation(jTextFieldURN.getLocation().x + jTextFieldURN.getWidth() + margin, clusterTop);
					
					jPanelScan.setLocation(jContentPane.getWidth() - jPanelScan.getWidth() - margin, jContentPane.getHeight() - jPanelScan.getHeight() - margin);
					
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
	
	private void search() {
		
		//Get the URN
		String urn = getJTextFieldURN().getText();
		
		if(urn.length() == 7) {
			
				try {
					
					//Get the voter from the wbb
					Voter newVoter = this.remoteBulletinBoard.voterLookup(urn);

					if(newVoter != null) {
						
						//Show a modal dialog box with the voter
						(new VisualVoter(this, newVoter, this.remoteBulletinBoard)).setVisible(true);
						
						//Clear the search box
						getJTextFieldURN().setText("");
						getJTextFieldURN().requestFocus();
						
					} else {
						
						//No voter was found
						JOptionPane.showMessageDialog(this, "No voter with this URN was found.", "No voter found", JOptionPane.INFORMATION_MESSAGE);

					}
					
				} catch (Exception e) {
					
					JOptionPane.showMessageDialog(this, "There was a problem with the connection to the database. Please restart the program. (" + e.getMessage() + ")", "Connection error.", JOptionPane.ERROR_MESSAGE);
					e.printStackTrace();
					
				}

		} else {
			
			//Wrong length URN entered
			JOptionPane.showMessageDialog(this, "A URN has 7 characters.", "Enter URN", JOptionPane.INFORMATION_MESSAGE);

		}
		
	}
	
	private void scan() {
		
		try {
			
			//Intermediate result and result
			String line;
			StringBuffer result = new StringBuffer();
			
			//Run the process and read the result if any
			Process p = Runtime.getRuntime().exec(this.externalScanCommand);
			BufferedReader input = new BufferedReader(new InputStreamReader(p.getInputStream()));
			while ((line = input.readLine()) != null) {
				result.append(line);
			}
			input.close();
			
			//Show the result
			jLabelScanOutput.setText(result.toString());
			
		} catch (Exception err) {
			err.printStackTrace();
			jLabelScanOutput.setText(err.getMessage());
		}

	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
