package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

/**
 * This event is fired when the race is updated
 * 
 * @author David Lundin
 *
 */
public class RaceUpdatedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param source
	 */
	public RaceUpdatedEvent(Object source) {
		super(source);
	}
	
}
