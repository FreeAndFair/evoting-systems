package uk.ac.surrey.pav.bulletinboard;

import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.tablemodels.AuditMachineTableModel;
import uk.ac.surrey.pav.bulletinboard.tablemodels.BoothTableModel;
import uk.ac.surrey.pav.bulletinboard.tablemodels.ElectionTableModel;
import uk.ac.surrey.pav.bulletinboard.tablemodels.TellerTableModel;

/**
 * Displays information about the current election(s) and
 * all entities involved in running it/them.
 * 
 * @author David Lundin
 *
 */
public class Dashboard extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The bulletin board that contains all data
	 */
	public BulletinBoard bulletinBoard;
	
	private JPanel jContentPane = null;

	private JButton jButtonStartElection = null;

	private JLabel jLabelTellers = null;

	private JScrollPane jScrollPaneTellers = null;

	private JTable jTableTellers = null;

	private JLabel jLabelBooths = null;

	private JScrollPane jScrollPaneBooths = null;

	private JTable jTableBooths = null;

	private JLabel jLabelAuditMachines = null;

	private JScrollPane jScrollPaneAuditMachines = null;

	private JTable jTableAuditMachines = null;

	private JButton jButtonCancel = null;

	private JScrollPane jScrollPaneElections = null;

	private JTable jTableElections = null;

	private JLabel jLabelElections = null;
	
	/**
	 * A reference to the server that we are running
	 */
	private BulletinBoardServer server;

	private JButton jButtonOpenTools = null;

	private JButton jButtonStopElection = null;
	
	/**
	 * The tools window
	 */
	private Tools tools = null;

	private JButton jButtonSettings = null;
	
	/**
	 * Settings
	 */
	private DashboardSettings settings = new DashboardSettings();

	/**
	 * This method initializes jButtonStartElection	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonStartElection() {
		if (jButtonStartElection == null) {
			jButtonStartElection = new JButton();
			jButtonStartElection.setBounds(new java.awt.Rectangle(555,540,121,31));
			jButtonStartElection.setText("Start server");
			jButtonStartElection.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					//Start the election
					startElection();
				}
			});
		}
		return jButtonStartElection;
	}

	/**
	 * This method initializes jScrollPaneTellers	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneTellers() {
		if (jScrollPaneTellers == null) {
			jScrollPaneTellers = new JScrollPane();
			jScrollPaneTellers.setBounds(new java.awt.Rectangle(15,195,481,91));
			jScrollPaneTellers.setViewportView(getJTableTellers());
		}
		return jScrollPaneTellers;
	}

	/**
	 * This method initializes jTableTellers	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableTellers() {
		if (jTableTellers == null) {
			jTableTellers = new JTable();
			jTableTellers.setModel(new TellerTableModel(bulletinBoard));
		}
		return jTableTellers;
	}

	/**
	 * This method initializes jScrollPaneBooths	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneBooths() {
		if (jScrollPaneBooths == null) {
			jScrollPaneBooths = new JScrollPane();
			jScrollPaneBooths.setBounds(new java.awt.Rectangle(15,315,481,91));
			jScrollPaneBooths.setViewportView(getJTableBooths());
		}
		return jScrollPaneBooths;
	}

	/**
	 * This method initializes jTableBooths	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableBooths() {
		if (jTableBooths == null) {
			jTableBooths = new JTable();
			jTableBooths.setModel(new BoothTableModel(bulletinBoard));
		}
		return jTableBooths;
	}

	/**
	 * This method initializes jScrollPaneAuditMachines	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneAuditMachines() {
		if (jScrollPaneAuditMachines == null) {
			jScrollPaneAuditMachines = new JScrollPane();
			jScrollPaneAuditMachines.setBounds(new java.awt.Rectangle(15,435,481,91));
			jScrollPaneAuditMachines.setViewportView(getJTableAuditMachines());
		}
		return jScrollPaneAuditMachines;
	}

	/**
	 * This method initializes jTableAuditMachines	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableAuditMachines() {
		if (jTableAuditMachines == null) {
			jTableAuditMachines = new JTable();
			jTableAuditMachines.setModel(new AuditMachineTableModel(bulletinBoard));
		}
		return jTableAuditMachines;
	}

	/**
	 * This method initializes jButtonCancel	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCancel() {
		if (jButtonCancel == null) {
			jButtonCancel = new JButton();
			jButtonCancel.setBounds(new java.awt.Rectangle(15,540,121,31));
			jButtonCancel.setText("Exit");
			jButtonCancel.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					System.exit(0);
				}
			});
		}
		return jButtonCancel;
	}

	/**
	 * This is the default constructor
	 */
	public Dashboard(BulletinBoard bulletinBoard) {
		super();
		
		//Store reference to the bulletin board that we got
		this.bulletinBoard = bulletinBoard;

		initialize();

	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(730, 618);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setResizable(true);
		this.setContentPane(getJContentPane());
		this.setTitle("Prêt à Voter Dashboard");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelElections = new JLabel();
			jLabelElections.setBounds(new java.awt.Rectangle(15,60,121,16));
			jLabelElections.setText("Elections");
			jLabelAuditMachines = new JLabel();
			jLabelAuditMachines.setBounds(new java.awt.Rectangle(15,420,121,16));
			jLabelAuditMachines.setText("Audit Machines");
			jLabelBooths = new JLabel();
			jLabelBooths.setBounds(new java.awt.Rectangle(15,300,121,16));
			jLabelBooths.setText("Booths");
			jLabelTellers = new JLabel();
			jLabelTellers.setBounds(new java.awt.Rectangle(15,180,121,16));
			jLabelTellers.setText("Tellers");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(getJButtonStartElection(), null);
			jContentPane.add(jLabelTellers, null);
			jContentPane.add(getJScrollPaneTellers(), null);
			jContentPane.add(jLabelBooths, null);
			jContentPane.add(getJScrollPaneBooths(), null);
			jContentPane.add(jLabelAuditMachines, null);
			jContentPane.add(getJScrollPaneAuditMachines(), null);
			jContentPane.add(getJButtonCancel(), null);
			jContentPane.add(getJScrollPaneElections(), null);
			jContentPane.add(jLabelElections, null);
			jContentPane.add(getJButtonOpenTools(), null);
			jContentPane.add(getJButtonStopElection(), null);
			jContentPane.add(getJButtonSettings(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					//Calculate size vars
					int margin = 15;
					int topMargin = margin;
					int bottomMargin = getJButtonCancel().getHeight() + (2 * margin);
					int tableWidth = jContentPane.getWidth() - (2 * margin);
					int tableHeight = (jContentPane.getHeight() - topMargin - jLabelElections.getHeight() - jLabelTellers.getHeight() - jLabelBooths.getHeight() - jLabelAuditMachines.getHeight() - bottomMargin - (3 * margin)) / 4;
					
					//Elections
					jLabelElections.setLocation(margin, topMargin);
					getJScrollPaneElections().setLocation(margin, jLabelElections.getLocation().y + jLabelElections.getHeight());
					getJScrollPaneElections().setSize(tableWidth, tableHeight);
					
					//Tellers
					jLabelTellers.setLocation(margin, getJScrollPaneElections().getLocation().y + getJScrollPaneElections().getHeight() + margin);
					getJScrollPaneTellers().setLocation(margin, jLabelTellers.getLocation().y + jLabelTellers.getHeight());
					getJScrollPaneTellers().setSize(tableWidth, tableHeight);
					
					//Booths
					jLabelBooths.setLocation(margin, getJScrollPaneTellers().getLocation().y + getJScrollPaneTellers().getHeight() + margin);
					getJScrollPaneBooths().setLocation(margin, jLabelBooths.getLocation().y + jLabelBooths.getHeight());
					getJScrollPaneBooths().setSize(tableWidth, tableHeight);
					
					//Audit machines
					jLabelAuditMachines.setLocation(margin, getJScrollPaneBooths().getLocation().y + getJScrollPaneBooths().getHeight() + margin);
					getJScrollPaneAuditMachines().setLocation(margin, jLabelAuditMachines.getLocation().y + jLabelAuditMachines.getHeight());
					getJScrollPaneAuditMachines().setSize(tableWidth, tableHeight);
					
					//Bottom buttons
					getJButtonCancel().setLocation(margin, jContentPane.getHeight() - getJButtonCancel().getHeight() - margin);
					getJButtonSettings().setLocation(getJButtonCancel().getLocation().x + getJButtonCancel().getWidth() + margin, jContentPane.getHeight() - getJButtonSettings().getHeight() - margin);
					getJButtonStartElection().setLocation(jContentPane.getWidth() - getJButtonStartElection().getWidth() - margin, jContentPane.getHeight() - getJButtonStartElection().getHeight() - margin);
					getJButtonStopElection().setLocation(getJButtonStartElection().getLocation().x - margin - getJButtonStartElection().getWidth(), getJButtonStartElection().getLocation().y);
					getJButtonOpenTools().setLocation(getJButtonStopElection().getLocation().x - margin - getJButtonOpenTools().getWidth(), getJButtonStopElection().getLocation().y);
					
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
	 * Start web bulletin board server
	 *
	 */
	private void startElection() {

		if(bulletinBoard.testStartElection()) {

			try {
				
				//Create a server object
				server = new BulletinBoardServer(bulletinBoard);

				//Bind it
				Naming.rebind("Bulletinboard", server);

				//Make the button unclickable
				this.getJButtonStartElection().setEnabled(false);
				this.getJButtonStopElection().setEnabled(true);
				
			} catch (RemoteException e) {
				e.printStackTrace();
			} catch (MalformedURLException e) {
				e.printStackTrace();
			}
			
		}

	}
	
	/**
	 * Stop the web bulletin board server
	 *
	 */
	private void stopElection() {
		
		try {
			
			//Unbind
			Naming.unbind("Bulletinboard");
			
			//Destroy
			server = null;
			
			//Make the button unclickable
			this.getJButtonStartElection().setEnabled(true);
			this.getJButtonStopElection().setEnabled(false);
			
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NotBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

	/**
	 * This method initializes jScrollPaneElections	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneElections() {
		if (jScrollPaneElections == null) {
			jScrollPaneElections = new JScrollPane();
			jScrollPaneElections.setBounds(new java.awt.Rectangle(15,75,481,91));
			jScrollPaneElections.setViewportView(getJTableElections());
		}
		return jScrollPaneElections;
	}

	/**
	 * This method initializes jTableElections	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableElections() {
		if (jTableElections == null) {
			jTableElections = new JTable();
			jTableElections.setModel(new ElectionTableModel(bulletinBoard));
		}
		return jTableElections;
	}

	/**
	 * This method initializes jButtonOpenTools	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOpenTools() {
		if (jButtonOpenTools == null) {
			jButtonOpenTools = new JButton();
			jButtonOpenTools.setBounds(new java.awt.Rectangle(285,540,121,31));
			jButtonOpenTools.setText("Tools");
			jButtonOpenTools.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					//Open tool window
					if(tools == null) {
						tools = new Tools(bulletinBoard);
					}
				
					tools.setVisible(true);
					
				}
			});
		}
		return jButtonOpenTools;
	}

	/**
	 * This method initializes jButtonStopElection	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonStopElection() {
		if (jButtonStopElection == null) {
			jButtonStopElection = new JButton();
			jButtonStopElection.setBounds(new java.awt.Rectangle(420,540,121,31));
			jButtonStopElection.setEnabled(false);
			jButtonStopElection.setText("Stop server");
			jButtonStopElection.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					stopElection();
					
				}
			});
		}
		return jButtonStopElection;
	}

	/**
	 * This method initializes jButtonSettings	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSettings() {
		if (jButtonSettings == null) {
			jButtonSettings = new JButton();
			jButtonSettings.setBounds(new java.awt.Rectangle(150,540,121,31));
			jButtonSettings.setText("Settings");
			jButtonSettings.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					(new DashboardSettingsDialog(settings)).setVisible(true);
					
				}
			});
		}
		return jButtonSettings;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
