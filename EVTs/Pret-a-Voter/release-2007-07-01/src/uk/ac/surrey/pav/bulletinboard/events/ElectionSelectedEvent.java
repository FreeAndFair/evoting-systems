package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

import uk.ac.surrey.pav.bulletinboard.entities.Election;

/**
 * This event is fired when an election is selected in the list
 * 
 * @author David Lundin
 *
 */
public class ElectionSelectedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * A reference to the election that has been selected
	 */
	Election election;
	
	/**
	 * Constructor
	 * 
	 * @param source The source of the event
	 * @param election The election that has been selected
	 */
	public ElectionSelectedEvent(Object source, Election election) {
		super(election);
		
		//Store reference to the election
		this.election = election;
	}
	
	/**
	 * Get the election
	 * 
	 * @return Election
	 */
	public Election getElection() {
		return this.election;
	}
	
}
