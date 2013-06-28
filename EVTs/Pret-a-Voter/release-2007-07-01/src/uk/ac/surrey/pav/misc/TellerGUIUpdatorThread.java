package uk.ac.surrey.pav.teller;

import javax.swing.JButton;
import javax.swing.JTable;

/**
 * Updates the TellerGUI user interface with information about the server
 * 
 * @author David Lundin
 *
 */
public class TellerGUIUpdatorThread extends Thread {

	/**
	 * Settings that are set out on screen
	 */
	private TellerSettings settings;
	
	/**
	 * The JTable to update with the status of the server
	 */
	private JTable statusTable;
	
	/**
	 * JButton used to start the server
	 */
	private JButton startButton;
	
	/**
	 * JButton used to stop the server
	 */
	private JButton stopButton;
	
	/**
	 * Keep the thread running while this is true
	 */
	private boolean keepRunning = true;
	
	/**
	 * Constructor
	 * 
	 * @param settings A TellerSettings object
	 */
	public TellerGUIUpdatorThread(TellerSettings settings, JTable statusTable, JButton startButton, JButton stopButton) {
		//Store the vars
		this.settings = settings;
		this.statusTable = statusTable;
		this.startButton = startButton;
		this.stopButton = stopButton;
	}
	
	/**
	 * The work of the thread
	 */
	public void run() {
		
		//Keep running
		while(keepRunning) {
			
			//Update the table
			this.statusTable.setModel(this.settings.getStatusList());
			
			//Make the appropriate button enabled
			if(this.settings.serverIsRunning()) {
				this.startButton.setEnabled(false);
				this.stopButton.setEnabled(true);
			} else {
				this.startButton.setEnabled(true);
				this.stopButton.setEnabled(false);
			}
			
			//Sleep for a bit
			try {
				this.sleep(5000);
			} catch (InterruptedException e) {
			}
		}
		
	}
}
