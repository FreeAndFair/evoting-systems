package uk.ac.surrey.pav.bulletinboard.tablemodels;

import javax.swing.table.AbstractTableModel;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.entities.AuditMachine;
import uk.ac.surrey.pav.bulletinboard.events.AuditMachineUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.AuditMachineUpdatedListener;

/**
 * Displays the audit machine list
 * 
 * @author David Lundin
 *
 */
public class AuditMachineTableModel extends AbstractTableModel implements AuditMachineUpdatedListener {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Column headers
	 */
	private String[] columnNames = {"ID", "Name", "Public key", "Forms audited"};

	/**
	 * All the audit machines
	 */
	private AuditMachine[] auditMachines;

	/**
	 * Handle the AuditMachineUpdatedEvent
	 */
	public void receiveAuditMachineUpdatedEvent(AuditMachineUpdatedEvent event) {
		this.fireTableDataChanged();
	}

	/**
	 * Returns the number of rows in the table
	 */
	public int getRowCount() {
		return this.auditMachines.length;
	}

	/**
	 * The number of columns in the table
	 */
	public int getColumnCount() {
		return 4;
	}

	/**
	 * The value in a particular cell
	 */
	public Object getValueAt(int rowIndex, int columnIndex) {
		switch(columnIndex) {
			case 1: return this.auditMachines[rowIndex].name; 
			case 2: return this.auditMachines[rowIndex].publicKey.toString(); 
			case 3: return "" + this.auditMachines[rowIndex].ballotCount; 
			default: return "" + this.auditMachines[rowIndex].auditMachineID;
		}
	}
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard
	 */
	public AuditMachineTableModel(BulletinBoard bulletinBoard) {
		//Store list of all the audit machines
		this.auditMachines = bulletinBoard.getAuditMachineArray();
		
		//Listen to updated events from all the tellers
		for(int x=0; x<this.auditMachines.length; x++) {
			this.auditMachines[x].addAuditMachineListener(this);
		}
	}
	
	/**
	 * Returns the name of a column
	 */
	public String getColumnName(int col) {
		return this.columnNames[col];
	}

}
