package uk.ac.surrey.pav.bulletinboard.events;

import java.util.EventObject;

/**
 * This event is fied when the audit machine status is updated
 * 
 * @author David Lundin
 *
 */
public class AuditMachineUpdatedEvent extends EventObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param source
	 */
	public AuditMachineUpdatedEvent(Object source) {
		super(source);
	}

}
