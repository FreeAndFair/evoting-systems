package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

/**
 * This event is fired when the teller status is updated
 * 
 * @author David Lundin
 *
 */
public class TellerUpdatedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param source
	 */
	public TellerUpdatedEvent(Object source) {
		super(source);
	}
	
}
