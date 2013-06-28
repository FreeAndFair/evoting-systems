package uk.ac.surrey.pav.bulletinboard.events;

/**
 * Listen to the election selected event
 * 
 * @author David Lundin
 *
 */
public interface ElectionSelectedListener {

	public void receiveElectionSelectedEvent(ElectionSelectedEvent event);

}
