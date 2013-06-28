package uk.ac.surrey.pav.bulletinboard;

import java.awt.event.ComponentEvent;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.batches.BatchCreator;
import uk.ac.surrey.pav.bulletinboard.batches.BatchCreatorUpdatorThread;
import uk.ac.surrey.pav.bulletinboard.challenges.ChallengeDialog;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.tablemodels.ElectionTableModel;
import uk.ac.surrey.pav.bulletinboard.tablemodels.RaceTableModel;
import uk.ac.surrey.pav.bulletinboard.tally.Tallier;
import uk.ac.surrey.pav.bulletinboard.tally.TallyDialog;

/**
 * Displays information about the loaded elections, their races and
 * the status of the associated batches.
 * 
 * @author David Lundin
 *
 */
public class Tools extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;
	
	/**
	 * The bulletin board settings and whatnot
	 */
	private BulletinBoard bulletinBoard;

	private JButton jButtonCreateBatch = null;

	private JButton jButtonClose = null;

	private JScrollPane jScrollPaneElections = null;

	private JTable jTableElections = null;

	private JLabel jLabelElections = null;

	private JLabel jLabelRaces = null;

	private JScrollPane jScrollPaneRaces = null;

	private JTable jTableRaces = null;
	
	/**
	 * Election table model
	 */
	private ElectionTableModel electionTableModel = null;
	
	/**
	 * Race table model
	 */
	private RaceTableModel raceTableModel = null;

	private JButton jButtonTally = null;

	private JButton jButtonChallenges = null;

	/**
	 * This is the default constructor
	 */
	public Tools(BulletinBoard bulletinBoard) {
		super();
		
		//Store the bulletin board
		this.bulletinBoard = bulletinBoard;

		//Initialise everything
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(831, 687);
		this.setResizable(true);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Tools");
		this.electionTableModel.addElectionSelectedListener(this.raceTableModel);
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelRaces = new JLabel();
			jLabelRaces.setBounds(new java.awt.Rectangle(30,180,181,16));
			jLabelRaces.setText("Races and batches");
			jLabelElections = new JLabel();
			jLabelElections.setBounds(new java.awt.Rectangle(30,30,181,16));
			jLabelElections.setText("Elections");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(getJButtonCreateBatch(), null);
			jContentPane.add(getJButtonClose(), null);
			jContentPane.add(getJScrollPaneElections(), null);
			jContentPane.add(jLabelElections, null);
			jContentPane.add(jLabelRaces, null);
			jContentPane.add(getJScrollPaneRaces(), null);
			jContentPane.add(getJButtonTally(), null);
			jContentPane.add(getJButtonChallenges(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					//Calculate size vars
					int margin = 15;
					int topMargin = margin;
					int bottomMargin = getJButtonCreateBatch().getHeight() + (2 * margin);
					int tableWidth = jContentPane.getWidth() - (2 * margin);
					int tableHeight = (jContentPane.getHeight() - topMargin - jLabelElections.getHeight() - margin - jLabelRaces.getHeight() - bottomMargin) / 2;
					
					//Set sizes and positions of tables and labels
					jLabelElections.setLocation(margin, topMargin);
					getJScrollPaneElections().setSize(tableWidth, tableHeight);
					getJScrollPaneElections().setLocation(margin, jLabelElections.getLocation().y + jLabelElections.getHeight());
					jLabelRaces.setLocation(margin, getJScrollPaneElections().getLocation().y + getJScrollPaneElections().getHeight() + margin);
					getJScrollPaneRaces().setSize(tableWidth, tableHeight);
					getJScrollPaneRaces().setLocation(margin, jLabelRaces.getLocation().y + jLabelRaces.getHeight());
					
					//Buttons
					getJButtonCreateBatch().setLocation(jContentPane.getWidth() - margin - getJButtonCreateBatch().getWidth(), jContentPane.getHeight() - margin - getJButtonCreateBatch().getHeight());
					getJButtonTally().setLocation(getJButtonCreateBatch().getLocation().x - getJButtonTally().getWidth() - margin, jContentPane.getHeight() - margin - getJButtonTally().getHeight());
					getJButtonChallenges().setLocation(getJButtonTally().getLocation().x - getJButtonChallenges().getWidth() - margin, jContentPane.getHeight() - margin - getJButtonChallenges().getHeight());
					getJButtonClose().setLocation(margin, jContentPane.getHeight() - margin - getJButtonClose().getHeight());
					
				}

				public void componentMoved(ComponentEvent e) {
				}

				public void componentShown(ComponentEvent e) {
				}

				public void componentHidden(ComponentEvent e) {
				}
			});
		}
		return jContentPane;
	}

	/**
	 * This method initializes jButtonCreateBatch	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCreateBatch() {
		if (jButtonCreateBatch == null) {
			jButtonCreateBatch = new JButton();
			jButtonCreateBatch.setBounds(new java.awt.Rectangle(480,450,121,31));
			jButtonCreateBatch.setText("Batch handler");
			jButtonCreateBatch.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					createBatch();
					
				}
			});
		}
		return jButtonCreateBatch;
	}
		
	public void createBatch() {
		
		try {
			
			if(this.getJTableElections().getSelectedRow() >= 0 && this.getJTableRaces().getSelectedRow() >= 0) {
				//The election for which ballot forms are batched up
				Election currentElection = this.bulletinBoard.getElectionFromID(this.getJTableElections().getSelectedRow());
				
				//If an election was found
				if(currentElection != null) {
					
					//Get the current race
					Race currentRace = currentElection.getRaceFromID(this.getJTableRaces().getSelectedRow());
					
					//As long as a race was found
					if(currentRace != null) {
						
						//Start a batch creator thread
						BatchCreator batchCreator = new BatchCreator(this.bulletinBoard.connection, currentRace, this.bulletinBoard.getTellerArray());
						BatchCreatorUpdatorThread updatorThread = new BatchCreatorUpdatorThread(batchCreator);
						updatorThread.start();
						(new Thread(batchCreator)).start();
						
					}
				}
			}
			
		} catch(Exception ex) {
			ex.printStackTrace();
		}
		
	}

	/**
	 * This method initializes jButtonClose	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonClose() {
		if (jButtonClose == null) {
			jButtonClose = new JButton();
			jButtonClose.setBounds(new java.awt.Rectangle(30,450,121,31));
			jButtonClose.setText("Close");
			jButtonClose.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					exit();
				}
			});
		}
		return jButtonClose;
	}

	/**
	 * This method initializes jScrollPaneElections	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneElections() {
		if (jScrollPaneElections == null) {
			jScrollPaneElections = new JScrollPane();
			jScrollPaneElections.setBounds(new java.awt.Rectangle(30,45,571,121));
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
			electionTableModel = new ElectionTableModel(bulletinBoard);
			jTableElections = new JTable(electionTableModel);
			jTableElections.getSelectionModel().addListSelectionListener(electionTableModel);
			jTableElections.setSelectionMode(javax.swing.ListSelectionModel.SINGLE_SELECTION);
		}
		return jTableElections;
	}

	/**
	 * This method initializes jScrollPaneRaces	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneRaces() {
		if (jScrollPaneRaces == null) {
			jScrollPaneRaces = new JScrollPane();
			jScrollPaneRaces.setBounds(new java.awt.Rectangle(30,195,571,196));
			jScrollPaneRaces.setViewportView(getJTableRaces());
		}
		return jScrollPaneRaces;
	}

	/**
	 * This method initializes jTableRaces	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableRaces() {
		if (jTableRaces == null) {
			raceTableModel = new RaceTableModel(bulletinBoard, RaceTableModel.INCLUDING_BATCHES);
			jTableRaces = new JTable(raceTableModel);
			jTableRaces.setCellSelectionEnabled(false);
			jTableRaces.setColumnSelectionAllowed(false);
			jTableRaces.setRowSelectionAllowed(true);
		}
		return jTableRaces;
	}
	
	private void exit() {
		this.setVisible(false);
	}

	/**
	 * This method initializes jButtonTally	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonTally() {
		if (jButtonTally == null) {
			jButtonTally = new JButton();
			jButtonTally.setBounds(new java.awt.Rectangle(345,450,121,31));
			jButtonTally.setText("Tally");
			jButtonTally.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					tallyRace();
					
				}
			});
		}
		return jButtonTally;
	}
	
	/**
	 * Opens a tally window etc
	 *
	 */
	private void tallyRace() {

		try {
			
			if(this.getJTableElections().getSelectedRow() >= 0 && this.getJTableRaces().getSelectedRow() >= 0) {
				//The election for which ballot forms are batched up
				Election currentElection = this.bulletinBoard.getElectionFromID(this.getJTableElections().getSelectedRow());
				
				//If an election was found
				if(currentElection != null) {
					
					//System.out.println("Found an election");
					
					//Get the current race
					Race currentRace = currentElection.getRaceFromID(this.getJTableRaces().getSelectedRow());
					
					//As long as a race was found
					if(currentRace != null) {
						
						//System.out.println("Found a race");

						//Check that the race is talliable
						if(currentRace.getNumberOfBatches() == bulletinBoard.getTellerCount()) {
							
							//Show a dialog
							(new TallyDialog(currentRace.tally)).setVisible(true);
							
							//Start a tallier
							Tallier tallier = new Tallier(this.bulletinBoard.connection, currentRace);
							(new Thread(tallier)).start();

						} else {
							
							//Display dialog box
							JOptionPane.showMessageDialog(this, "This race has not been fully decrypted yet, please invoke the batch handler first.", "Tally", JOptionPane.ERROR_MESSAGE);
							
						}
						
					}
				}
			}
			
		} catch(Exception ex) {
			ex.printStackTrace();
		}

	}

	/**
	 * Opens the window for the challenges to be created etc
	 *
	 */
	private void performChallenges() {

		try {
			
			if(this.getJTableElections().getSelectedRow() >= 0 && this.getJTableRaces().getSelectedRow() >= 0) {
				//The election for which ballot forms are batched up
				Election currentElection = this.bulletinBoard.getElectionFromID(this.getJTableElections().getSelectedRow());
				
				//If an election was found
				if(currentElection != null) {
					
					//System.out.println("Found an election");
					
					//Get the current race
					Race currentRace = currentElection.getRaceFromID(this.getJTableRaces().getSelectedRow());
					
					//As long as a race was found
					if(currentRace != null) {
						
						//System.out.println("Found a race");

						//Check that the race is talliable
						if(currentRace.getNumberOfBatches() == bulletinBoard.getTellerCount()) {
							
							//Show a dialog
							(new ChallengeDialog(bulletinBoard, currentRace)).setVisible(true);
							
						} else {
							
							//Display dialog box
							JOptionPane.showMessageDialog(this, "This race has not been fully decrypted yet, please invoke the batch handler first.", "Challenges", JOptionPane.ERROR_MESSAGE);
							
						}
						
					}
				}
			}
			
		} catch(Exception ex) {
			ex.printStackTrace();
		}

	}

	/**
	 * This method initializes jButtonChallenges	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonChallenges() {
		if (jButtonChallenges == null) {
			jButtonChallenges = new JButton();
			jButtonChallenges.setBounds(new java.awt.Rectangle(210,450,121,31));
			jButtonChallenges.setText("Challenges");
			jButtonChallenges.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					performChallenges();
					
				}
			});
		}
		return jButtonChallenges;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
