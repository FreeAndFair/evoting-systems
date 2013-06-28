package uk.ac.surrey.pav.bulletinboard.tablemodels;

import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.challenges.Challenge;
import uk.ac.surrey.pav.bulletinboard.entities.Batch;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.events.ElectionSelectedEvent;
import uk.ac.surrey.pav.bulletinboard.events.ElectionSelectedListener;
import uk.ac.surrey.pav.bulletinboard.events.RaceUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.RaceUpdatedListener;

/**
 * Displays the race list
 * 
 * @author David Lundin
 *
 */
public class RaceTableModel extends AbstractTableModel implements RaceUpdatedListener, ElectionSelectedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Constant representing display mode
	 */
	public static final boolean EXCLUDING_BATCHES = false;

	/**
	 * Constant representing display mode
	 */
	public static final boolean INCLUDING_BATCHES = true;
	
	/**
	 * The number of columns shown before the tellers in the view
	 */
	private static final int PRE_TELLER_COLUMNS = 5;
	
	/**
	 * Display mode
	 */
	private boolean displayBatches;
	
	/**
	 * Reference to the current election
	 */
	private Election election;

	/**
	 * All the races
	 */
	private Race[] races;
	
	/**
	 * All the tellers
	 */
	private Teller[] tellers;
	
	/**
	 * Column headers
	 */
	private String[] columnNames = {"ID", "Name", "Candidates", "Ballots cast", "Batches"};
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard BulletinBoard with all information about the elections
	 */
	public RaceTableModel(BulletinBoard bulletinBoard, boolean displayBatches) {
		//Default constructor used to create empty table before selection has been made
		this.displayBatches = displayBatches;
		
		if(displayBatches) {
			//Store a list of the tellers
			this.tellers = bulletinBoard.getTellerArray();
		}
	}
	
	/**
	 * Returns the number of rows in the table
	 */
	public int getRowCount() {
		if(this.races != null) {
			return this.races.length;
		} else {
			return 0;
		}
	}

	/**
	 * Returns the number of columns in the table
	 */
	public int getColumnCount() {
		if(this.displayBatches && this.tellers != null) {
			//Batches in their own columns
			return this.PRE_TELLER_COLUMNS + (2 * this.tellers.length);
		} else {
			//No batches shown
			return this.PRE_TELLER_COLUMNS;
		}
	}

	/**
	 * Returns the value of a cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		if(columnIndex < this.PRE_TELLER_COLUMNS) {
			switch(columnIndex) {
				case 1: return this.races[rowIndex].name; 
				case 2: return "" + this.races[rowIndex].candidates.size(); 
				case 3: return "" + this.races[rowIndex].ballotCount; 
				case 4: return "" + this.races[rowIndex].getNumberOfBatches(); 
				default: return "" + this.races[rowIndex].raceID;
			}
		} else {
			
			//The current teller to set out batch info about
			int tellerIndex = (columnIndex - this.PRE_TELLER_COLUMNS) / 2;
			int batchOrChallenge = (columnIndex - this.PRE_TELLER_COLUMNS) % 2;

			//The result we will send back
			StringBuffer result = new StringBuffer();
			
			if(batchOrChallenge == 0) {

				//Get the Batch object
				Batch currentBatch = this.races[rowIndex].getBatchFromTellerID(tellerIndex);
				
				//Add the batch part of the result
				if(currentBatch != null) {
					result.append("OK");
				} else {
					result.append("---");
				}

			} else {

				//Get the challenge object
				Challenge currentChallenge = this.races[rowIndex].getChallengeFromTellerID(tellerIndex);
				
				//Add the challenge part of the result
				if(currentChallenge != null) {
					
					//A challenge object exists, check how complete it is
					if(currentChallenge.commitment != null && currentChallenge.bitmap != null) {
						
						//Both the commitment and the value are set
						result.append("OK");
						
					} else if(currentChallenge.commitment != null) {
						
						//Only the commitment is set
						result.append("Comm.");
						
					} else {
						
						//Neither is set
						result.append("---");
						
					}
					
				} else {
					
					//There is no challenge for this teller
					result.append("---");
					
				}

			}
			
			//Done, return
			return result;
			
		}
		
	}
	
	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		if(col < this.PRE_TELLER_COLUMNS) {
			return this.columnNames[col];
		} else {
			return this.tellers[(col - this.PRE_TELLER_COLUMNS) / 2].name;
		}
	}

	/**
	 * Handles the event generated when a race is updated
	 * 
	 * @param event
	 */
	public void receiveRaceUpdatedEvent(RaceUpdatedEvent event) {
		//Fire an event to update the table
		this.fireTableDataChanged();
	}

	/**
	 * Handles the event generated when an election is selected elsewhere
	 * 
	 * @param event
	 */
	public void receiveElectionSelectedEvent(ElectionSelectedEvent event) {
		
		//Check if this is a new election, if so update
		if(event.getElection() != this.election) {
			
			//Store reference to this new election
			this.election = event.getElection();
			
			//No longer listen to changes to the previous races
			if(this.races != null) {
				for(int x=0; x<this.races.length; x++) {
					this.races[x].removeRaceUpdatedListener(this);
				}
			}
			
			//Store a list of all the races
			this.races = this.election.getRaceArray();
	
			//Listen to changes to these elections
			for(int x=0; x<this.races.length; x++) {
				this.races[x].addRaceUpdatedListener(this);
			}
	
			//Fire the event to update the table
			this.fireTableDataChanged();
			
		}
		
	}

}
