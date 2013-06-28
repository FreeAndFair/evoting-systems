package uk.ac.surrey.pav.bulletinboard.tally;

import java.util.ArrayList;
import java.util.Iterator;

import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.events.TallyUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.TallyUpdatedListener;

/**
 * Stores information about a tally
 * 
 * @author David Lundin
 *
 */
public class Tally {

	/**
	 * The rounds in this tally
	 */
	public ArrayList rounds = new ArrayList();
	
	/**
	 * Those listening to changes
	 */
	private ArrayList tallyUpdatedListeners = new ArrayList();
	
	/**
	 * The race we are tallying
	 */
	public Race race;
	
	/**
	 * Add a round that has been completed in this tally
	 * 
	 * @param name
	 * @param scores
	 * @param description
	 */
	public void addRound(String name, int[] scores, int discarded, String description) {
		//Store the round
		this.rounds.add(new TallyRound(name, scores, discarded, description));
		
		//Tell everyone who is listening
		this.fireTallyUpdatedEvent();
	}
	
	/**
	 * Add a listener
	 * 
	 * @param listener
	 */
	public void addTallyUpdatedListener(TallyUpdatedListener listener) {
		this.tallyUpdatedListeners.add(listener);
	}
	
	/**
	 * Remove a listener
	 * 
	 * @param listener
	 */
	public void removeTallyUpdatedListener(TallyUpdatedListener listener) {
		this.tallyUpdatedListeners.remove(listener);
	}
	
	/**
	 * Fires the TallyUpdatedEvent
	 *
	 */
	private void fireTallyUpdatedEvent() {
		
		//All the listeners
		Iterator listeners = this.tallyUpdatedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((TallyUpdatedListener)listeners.next()).receiveTallyUpdatedEvent(new TallyUpdatedEvent(this));
		}

	}
	
	/**
	 * Constructor
	 * 
	 * @param race
	 */
	public Tally(Race race) {
		//Store referece
		this.race = race;
	}
	
	/**
	 * Removes previous rounds
	 *
	 */
	public void clear() {
		this.rounds.clear();
	}
	
}
