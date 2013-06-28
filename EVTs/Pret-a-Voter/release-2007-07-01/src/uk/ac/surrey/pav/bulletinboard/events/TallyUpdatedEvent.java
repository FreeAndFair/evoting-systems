package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

/**
 * This event is fired when the tally is updated
 * 
 * @author David Lundin
 *
 */
public class TallyUpdatedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param source
	 */
	public TallyUpdatedEvent(Object source) {
		super(source);
	}

}
