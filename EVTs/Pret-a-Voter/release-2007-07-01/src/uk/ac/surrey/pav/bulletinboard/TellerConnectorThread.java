package uk.ac.surrey.pav.bulletinboard;

import uk.ac.surrey.pav.bulletinboard.entities.Teller;

/**
 * One thread is started for each teller, checking repeatedly
 * the connection status of the associated teller. If not connected it attempts
 * to connect the teller over RMI.
 * 
 * @author David Lundin
 *
 */
public class TellerConnectorThread extends Thread {

	/**
	 * Teller that this connects
	 */
	Teller teller;
	
	/**
	 * Keep running while this is true
	 */
	boolean keepRunning = true;
	
	/**
	 * Constructor
	 * 
	 * @param teller The parent teller
	 */
	public TellerConnectorThread(Teller teller) {
		//Store the reference
		this.teller = teller;
	}

	/**
	 * Attempts to connect to the teller
	 */
	public void run() {
		
		//Retry connecting every second
		while(keepRunning) {
		
			//Check if status is NOT CONNECTED
			if(!this.teller.connectionStatus) {
				
				//Try to reconnect
				try {
					
					teller.connect();
					
					if(this.teller.connectionStatus) {
						
						//Try to shake hands
						teller.doHandshake();
						
					}

				} catch (Exception e) {}

			} else if(!this.teller.handshakeStatus) {
				
				//Try to shake hands
				try {
					
					teller.doHandshake();
					
				} catch (Exception e) {}
				
			} else {
				
				//We appear to be properly set up, from now simply shake hands every now and then
				try {
					
					teller.doHandshake();
					
				} catch (Exception e) {}
				
			}
			
			//Sleep for a bit
			try {
				this.sleep(1000);
			} catch (InterruptedException e) {}

		}
		
	}
}
