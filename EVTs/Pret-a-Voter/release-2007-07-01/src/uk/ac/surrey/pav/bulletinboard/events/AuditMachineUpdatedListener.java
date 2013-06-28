package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listen to the audit machine updated event
 * 
 * @author David Lundin
 *
 */
public interface AuditMachineUpdatedListener {

	public void receiveAuditMachineUpdatedEvent(AuditMachineUpdatedEvent event);
	
}
