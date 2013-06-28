package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

/**
 * This event is fired when the booth status is updated
 * 
 * @author David Lundin
 *
 */
public class BoothUpdatedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param source
	 */
	public BoothUpdatedEvent(Object source) {
		super(source);
	}

}
