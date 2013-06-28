package uk.ac.surrey.pav.teller;

/**
 * Listens to the teller updated event
 * 
 * @author David Lundin
 *
 */
public interface TellerUpdatedListener {

	public void receiveTellerUpdatedEvent(TellerUpdatedEvent event);
	
}
