package uk.ac.surrey.pav.bulletinboard.tablemodels;

import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.entities.Booth;
import uk.ac.surrey.pav.bulletinboard.events.BoothUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.BoothUpdatedListener;

/**
 * Displays the voting booth list
 * 
 * @author David Lundin
 *
 */
public class BoothTableModel extends AbstractTableModel implements BoothUpdatedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Column headers
	 */
	private String[] columnNames = {"ID", "Name", "Public key", "Ballots cast"};

	/**
	 * Array of all the booths set out
	 */
	private Booth[] booths;

	/**
	 * Deals with the BoothUpdatedEvent
	 */
	public void receiveBoothUpdatedEvent(BoothUpdatedEvent event) {
		this.fireTableDataChanged();
	}

	/**
	 * The number of rows in the table
	 */
	public int getRowCount() {
		return this.booths.length;
	}

	/**
	 * The number of columns in the table
	 */
	public int getColumnCount() {
		return 4;
	}

	/**
	 * The value of a cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		switch(columnIndex) {
			case 1: return this.booths[rowIndex].name; 
			case 2: return this.booths[rowIndex].publicKey.toString(); 
			case 3: return "" + this.booths[rowIndex].ballotCount; 
			default: return "" + this.booths[rowIndex].boothID;
		}
	}
	
	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		return this.columnNames[col];
	}
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard
	 */
	public BoothTableModel(BulletinBoard bulletinBoard) {
		//Store a list of all the booths
		this.booths = bulletinBoard.getBoothArray();
		
		//Listen to all the booths
		for(int x=0; x<this.booths.length; x++) {
			this.booths[x].addBoothUpdatedListener(this);
		}
	}

}
