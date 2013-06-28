package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listens to the booth updated event
 * 
 * @author David Lundin
 *
 */
public interface BoothUpdatedListener {

	public void receiveBoothUpdatedEvent(BoothUpdatedEvent event);

}
