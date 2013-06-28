package uk.ac.surrey.pav.bulletinboard.tablemodels;

import java.util.ArrayList;
import java.util.Iterator;

import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.events.ElectionSelectedEvent;
import uk.ac.surrey.pav.bulletinboard.events.ElectionSelectedListener;
import uk.ac.surrey.pav.bulletinboard.events.ElectionUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.ElectionUpdatedListener;

/**
 * Displays the election list
 * 
 * @author David Lundin
 *
 */
public class ElectionTableModel extends AbstractTableModel implements ElectionUpdatedListener, ListSelectionListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The bulletin board
	 */
	private BulletinBoard bulletinBoard;
	
	/**
	 * All the elections
	 */
	private Election[] elections;
	
	/**
	 * Column headers
	 */
	private String[] columnNames = {"ID", "Name", "Start date", "End date", "Ballots cast", "Ballots audited"};
	
	/**
	 * List of listeners for the ElectionSelectedEvent
	 */
	private ArrayList electionSelectedListeners = new ArrayList();
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard BulletinBoard with all information about the elections
	 */
	public ElectionTableModel(BulletinBoard bulletinBoard) {
		//Store reference to the bulletin board
		this.bulletinBoard = bulletinBoard;
		
		//Store a list of all the elections
		this.elections = bulletinBoard.getElectionArray();
		
		//Listen to changes to these elections
		for(int x=0; x<this.elections.length; x++) {
			this.elections[x].addElectionUpdatedListener(this);
		}
	}
	
	/**
	 * Returns the number of rows in the table
	 */
	public int getRowCount() {
		return this.elections.length;
	}

	/**
	 * Returns the number of columns in the table
	 */
	public int getColumnCount() {
		return 6;
	}

	/**
	 * Returns the value of a cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		switch(columnIndex) {
			case 1: return this.elections[rowIndex].name; 
			case 2: return this.elections[rowIndex].startDate; 
			case 3: return this.elections[rowIndex].endDate; 
			case 4: return "" + this.elections[rowIndex].ballotCount; 
			case 5: return "" + this.elections[rowIndex].ballotAuditCount; 
			default: return "" + this.elections[rowIndex].electionID;
		}
	}
	
	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		return this.columnNames[col];
	}

	/**
	 * Handles the event generated when an election is updated
	 */
	public void receiveElectionUpdatedEvent(ElectionUpdatedEvent event) {
		this.fireTableDataChanged();
	}
	
	/**
	 * Adds a listener for the election selected event
	 * 
	 * @param listener
	 */
	public void addElectionSelectedListener(ElectionSelectedListener listener) {
		this.electionSelectedListeners.add(listener);
	}

	/**
	 * Removes a listener for the election selected event
	 * 
	 * @param listener
	 */
	public void removeElectionSelectedListener(ElectionSelectedListener listener) {
		this.electionSelectedListeners.remove(listener);
	}
	
	/**
	 * Fires the ElectionSelectedEvent
	 * 
	 * @param election The election that has been selected
	 */
	private void fireElectionSelectedEvent(Election election) {
		//All the listeners
		Iterator listeners = this.electionSelectedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((ElectionSelectedListener)listeners.next()).receiveElectionSelectedEvent(new ElectionSelectedEvent(this, election));
		}

	}

	/**
	 * An election has been selected, update
	 */
	public void valueChanged(ListSelectionEvent e) {
		if(e.getFirstIndex() >= 0) {
			this.fireElectionSelectedEvent(this.elections[e.getFirstIndex()]);
		}
	}

}
