package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

/**
 * This event is fired when the election status is updated
 * 
 * @author David Lundin
 *
 */
public class ElectionUpdatedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param source
	 */
	public ElectionUpdatedEvent(Object source) {
		super(source);
	}
	
}
