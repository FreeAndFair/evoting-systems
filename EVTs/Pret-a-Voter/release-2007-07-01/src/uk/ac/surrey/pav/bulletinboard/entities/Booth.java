package uk.ac.surrey.pav.bulletinboard.entities;

import java.security.PublicKey;
import java.util.ArrayList;
import java.util.Iterator;

import uk.ac.surrey.pav.bulletinboard.events.BoothUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.BoothUpdatedListener;

/**
 * Keeps information about the voting booth that the bulletin board
 * knows about.
 * 
 * @author David Lundin
 *
 */
public class Booth {

	/**
	 * ID of the booth
	 */
	public int boothID;
	
	/**
	 * Name or description of the booth.
	 */
	public String name;
	
	/**
	 * Public key
	 */
	public PublicKey publicKey;
	
	/**
	 * Count the number of ballots cast from this booth
	 */
	public int ballotCount = 0;
	
	/**
	 * A list of the listeners for the BoothUpdatedEvent
	 */
	private ArrayList boothUpdatedListeners = new ArrayList();
	
	/**
	 * Constructor
	 * 
	 * @param boothID
	 * @param name
	 */
	public Booth(int ballotCount, int boothID, String name, PublicKey publicKey) {
		this.ballotCount = ballotCount;
		this.boothID = boothID;
		this.name = name;
		this.publicKey = publicKey;
	}
	
	/**
	 * Increments the ballot count for this booth
	 *
	 */
	public void incrementBallotCount() {
		//Increment the counter
		this.ballotCount++;
		
		//Tell anyone who is listening
		this.fireBoothUpdatedEvent();
	}
	
	/**
	 * Add a listener for the BoothUpdatedEvent
	 * 
	 * @param listener
	 */
	public void addBoothUpdatedListener(BoothUpdatedListener listener) {
		this.boothUpdatedListeners.add(listener);
	}

	/**
	 * Remove a listener for the BoothUpdatedEvent
	 * 
	 * @param listener
	 */
	public void removeBoothUpdatedListener(BoothUpdatedListener listener) {
		this.boothUpdatedListeners.remove(listener);
	}
	
	/**
	 * Fires the BoothUpdatedEvent
	 *
	 */
	private void fireBoothUpdatedEvent() {
		//All the listeners
		Iterator listeners = this.boothUpdatedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((BoothUpdatedListener)listeners.next()).receiveBoothUpdatedEvent(new BoothUpdatedEvent(this));
		}
	}
}
