package uk.ac.surrey.pav.bulletinboard.tablemodels;

import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.events.TellerUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.TellerUpdatedListener;

/**
 * Displays the teller list
 * 
 * @author David Lundin
 *
 */
public class TellerTableModel extends AbstractTableModel implements TellerUpdatedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Column headers
	 */
	private String[] columnNames = {"ID", "Name", "IP Address", "Server name", "Sequence no", "Public key", "Connection", "Handshake", "Conn-errors"};
	
	/**
	 * The tellers set out by this model
	 */
	private Teller[] tellers;
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard A BulletinBoard containing all the tellers
	 */
	public TellerTableModel(BulletinBoard bulletinBoard) {
		//Store an array of all the tellers in the list
		this.tellers = bulletinBoard.getTellerArray();
		
		//Listen to updated events from all the tellers
		for(int x=0; x<this.tellers.length; x++) {
			this.tellers[x].addTellerUpdatedListener(this);
		}
	}

	/**
	 * The number of rows
	 */
	public int getRowCount() {
		return this.tellers.length;
	}

	/**
	 * The number of columns
	 */
	public int getColumnCount() {
		return 9;
	}

	/**
	 * Returns the value for a particular cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		switch(columnIndex) {
			case 1: return this.tellers[rowIndex].name; 
			case 2: return this.tellers[rowIndex].address; 
			case 3: return this.tellers[rowIndex].serverName; 
			case 4: return "" + this.tellers[rowIndex].sequenceNumber; 
			case 5: return this.tellers[rowIndex].publicKey.toString(); 
			case 6: return this.tellers[rowIndex].connectionState; 
			case 7: if(this.tellers[rowIndex].handshakeStatus) {
				return "OK"; 
			} else {
				return "Failed";
			}
			case 8: return "" + this.tellers[rowIndex].connectionErrorCount; 
			default: return "" + this.tellers[rowIndex].tellerID;
		}
	}
		
	/**
	 * Deals with the updating of a teller
	 */
	public void receiveTellerUpdatedEvent(TellerUpdatedEvent event) {
		this.fireTableDataChanged();
	}

	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		return this.columnNames[col];
	}

}
