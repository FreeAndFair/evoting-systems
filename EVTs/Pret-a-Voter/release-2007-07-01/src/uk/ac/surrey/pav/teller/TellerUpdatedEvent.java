package uk.ac.surrey.pav.teller;

import java.util.EventObject;

/**
 * This event is fired when the teller's status is changed
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
	 * @param arg0
	 */
	public TellerUpdatedEvent(Object arg0) {
		super(arg0);
	}

}
