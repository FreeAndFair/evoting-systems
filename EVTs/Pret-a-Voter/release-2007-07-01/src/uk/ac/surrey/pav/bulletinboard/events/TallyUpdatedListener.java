package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listens to the tally updated event
 * 
 * @author David Lundin
 *
 */
public interface TallyUpdatedListener {

	public void receiveTallyUpdatedEvent(TallyUpdatedEvent event);
	
}
