package uk.ac.surrey.pav.misc;

import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;

/**
 * Connects to all tellers and checks the status of all
 * teller connections regularly.
 * 
 * @author David Lundin
 *
 */
public class DashboardUpdatorThread extends Thread {

	/**
	 * The bulletin board object
	 */
	private BulletinBoard bulletinBoard;
	
	/**
	 * Tables to update
	 */
	private JTable electionTable;
	private JTable tellerTable;
	private JTable boothTable;
	private JTable auditMachineTable;
	
	/**
	 * Keep running while this variable is true
	 */
	private boolean keepUpdating = true;
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard BulletinBoard object containing all settings
	 * @param electionTable JTable into which to set out information about elections
	 * @param tellerTable JTable into which to set out information about tellers
	 * @param boothTable JTable into which to set out information about booths
	 * @param auditMachineTable JTable into which to set out information about audit machines
	 */
	public DashboardUpdatorThread(BulletinBoard bulletinBoard, JTable electionTable, JTable tellerTable, JTable boothTable, JTable auditMachineTable) {
		//Store references
		this.bulletinBoard = bulletinBoard;
		this.electionTable = electionTable;
		this.boothTable = boothTable;
		this.auditMachineTable = auditMachineTable;
		this.tellerTable = tellerTable;
	}
	
	/**
	 * Updates the JTables
	 *
	 */
	private void updateTable() {
		
		//Update the tables
		//this.electionTable.setModel(this.bulletinBoard.getElectionList());
		//this.tellerTable.setModel(this.bulletinBoard.getTellerList());
		//this.boothTable.setModel(this.bulletinBoard.getBoothList());
		//this.auditMachineTable.setModel(this.bulletinBoard.getAuditMachineList());
		
	}
	
	/**
	 * The work performed by this thread: to attempt to connect to all the tellers
	 * and then to maintain the connections if they happen to go down
	 */
	public void run() {
		
		//Keep updating etc
		while(this.keepUpdating) {
			
			//Update the table
			//this.updateTable();

			//Sleep for a while
			try {
				this.sleep(10000);
			} catch (InterruptedException e) {
			}
			
		}
		
	}
}
