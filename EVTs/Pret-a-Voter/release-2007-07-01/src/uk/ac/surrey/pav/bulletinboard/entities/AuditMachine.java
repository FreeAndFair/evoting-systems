package uk.ac.surrey.pav.bulletinboard.entities;

import java.security.PublicKey;
import java.util.ArrayList;
import java.util.Iterator;

import uk.ac.surrey.pav.bulletinboard.events.AuditMachineUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.AuditMachineUpdatedListener;

/**
 * Keeps information about the audit machine
 * 
 * @author David Lundin
 *
 */
public class AuditMachine {

	/**
	 * Audit machine ID (primary key in database)
	 */
	public int auditMachineID;
	
	/**
	 * Name or description of the audit machine
	 */
	public String name;
	
	/**
	 * Public key of the audit machine
	 */
	public PublicKey publicKey;
	
	/**
	 * Count of the number of ballot forms audited by this machine
	 */
	public int ballotCount = 0;
	
	/**
	 * Listeners for the AuditMachineUpdatedEvent
	 */
	private ArrayList auditMachineUpdatedListeners = new ArrayList();
	
	/**
	 * Constructor
	 * 
	 * @param auditMachineID
	 * @param name
	 * @param publicKey
	 */
	public AuditMachine(int ballotCount, int auditMachineID, String name, PublicKey publicKey) {
		this.ballotCount = ballotCount;
		this.auditMachineID = auditMachineID;
		this.name = name;
		this.publicKey = publicKey;
	}
	
	/**
	 * Increments the count of the number of ballot forms audited by this machine
	 *
	 */
	public void incrementBallotCount() {
		//Increment the counter
		this.ballotCount++;
		
		//Tell anyone who is listening
		this.fireAuditMachineUpdatedEvent();
	}
	
	/**
	 * Add a listener for the AuditMachineUpdatedEvent
	 * 
	 * @param listener
	 */
	public void addAuditMachineListener(AuditMachineUpdatedListener listener) {
		this.auditMachineUpdatedListeners.add(listener);
	}

	/**
	 * Remove a listener for the AuditMachineUpdatedEvent
	 * 
	 * @param listener
	 */
	public void removeAuditMachineListener(AuditMachineUpdatedListener listener) {
		this.auditMachineUpdatedListeners.remove(listener);
	}
	
	/**
	 * Fires the AuditMachineUpdatedEvent
	 *
	 */
	private void fireAuditMachineUpdatedEvent() {
		//All the listeners
		Iterator listeners = this.auditMachineUpdatedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((AuditMachineUpdatedListener)listeners.next()).receiveAuditMachineUpdatedEvent(new AuditMachineUpdatedEvent(this));
		}
	}

}
