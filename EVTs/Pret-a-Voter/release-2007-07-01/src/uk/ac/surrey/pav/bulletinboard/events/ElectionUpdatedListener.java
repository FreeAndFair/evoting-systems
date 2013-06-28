package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listen to the election updated event
 * 
 * @author David Lundin
 *
 */
public interface ElectionUpdatedListener {

	public void receiveElectionUpdatedEvent(ElectionUpdatedEvent event);
	
}
