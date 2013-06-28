package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listens to the teller updated event
 * 
 * @author David Lundin
 *
 */
public interface TellerUpdatedListener {

	public void receiveTellerUpdatedEvent(TellerUpdatedEvent event);

}
