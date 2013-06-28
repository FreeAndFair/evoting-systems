package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listens to the race updated event
 * 
 * @author David Lundin
 *
 */
public interface RaceUpdatedListener {

	public void receiveRaceUpdatedEvent(RaceUpdatedEvent event);
	
}
