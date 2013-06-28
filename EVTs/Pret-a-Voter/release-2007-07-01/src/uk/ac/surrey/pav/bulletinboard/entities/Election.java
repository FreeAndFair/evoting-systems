package uk.ac.surrey.pav.bulletinboard.entities;

import java.util.ArrayList;
import java.util.Date;
import java.util.Iterator;

import uk.ac.surrey.pav.bulletinboard.events.ElectionUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.ElectionUpdatedListener;


/**
 * Stores information about the current election(s).
 * 
 * @author David Lundin
 *
 */
public class Election {

	/**
	 * Election ID, primary key in the database
	 */
	public int electionID;
	
	/**
	 * Name or description of the election
	 */
	public String name;
	
	/**
	 * Start date of the election
	 */
	public Date startDate;
	
	/**
	 * End date of the election
	 */
	public Date endDate;
	
	/**
	 * The races in this election
	 */
	public ArrayList races = new ArrayList();
	
	/**
	 * A count of the ballots cast in this election
	 */
	public int ballotCount = 0;
	
	/**
	 * A count of the number of ballot forms audited in this election
	 */
	public int ballotAuditCount = 0;
	
	/**
	 * List of ElectionUpdatedListeners
	 */
	private ArrayList electionUpdatedListeners = new ArrayList();
	
	/**
	 * Constructor
	 * 
	 * @param electionID	ID of the election in the database
	 * @param name			Name or description of the election
	 * @param startDate		Start date of the election phase
	 * @param endDate		End date of the election phase
	 */
	public Election(int ballotCount, int ballotAuditCount, int electionID, String name, Date startDate, Date endDate) {
		//Store values
		this.electionID = electionID;
		this.ballotAuditCount = ballotAuditCount;
		this.ballotCount = ballotCount;
		this.name = name;
		this.startDate = startDate;
		this.endDate = endDate;
	}
	
	/**
	 * Stores a new race
	 * @param newRace Race object
	 */
	public void addRace(Race newRace) {
		this.races.add(newRace);
	}
	
	/**
	 * Finds a race in this election with a particular ID
	 * 
	 * @param raceID	The ID of the race sought
	 * @return				Race object
	 */
	public Race getRaceFromID(int raceID) {
		//Go through all elections
		for(int x=0; x<this.races.size(); x++) {
			if(((Race)this.races.get(x)).raceID == raceID) {
				return (Race)this.races.get(x);
			}
		}
		return null;
	}
	
	/**
	 * Returns true if the election is currently in a phase where
	 * it accepts ballots to be cast
	 * 
	 * @return Boolean true if votes may be cast
	 */
	public boolean isAcceptingVotes() {
		Date currentDate = new Date();
		if((this.startDate.before(currentDate) || this.startDate.equals(currentDate))
				&& (this.endDate.after(currentDate) || this.endDate.equals(currentDate))) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Increments the count of the number of ballot forms cast in this election by one
	 *
	 */
	public void incrementBallotCount() {
		//Increment the count
		this.ballotCount++;
		
		//Tell anyone who is listening
		this.fireElectionUpdatedEvent();
	}
	
	/**
	 * Increments the count of the number of ballot forms audited in this election
	 *
	 */
	public void incrementBallotAuditCount() {
		//Increment the count
		this.ballotAuditCount++;
		
		//Tell anyone who is listening
		this.fireElectionUpdatedEvent();
	}
	
	/**
	 * Adds a listener for the ElectionUpdatedEvent
	 * @param listener
	 */
	public void addElectionUpdatedListener(ElectionUpdatedListener listener) {
		this.electionUpdatedListeners.add(listener);
	}
	
	/**
	 * Removes a listener for the ElectionUpdatedEvent
	 * @param listener
	 */
	public void removeElectionUpdatedListener(ElectionUpdatedListener listener) {
		this.electionUpdatedListeners.remove(listener);
	}
	
	/**
	 * Fires the ElectionUpdatedEvent
	 *
	 */
	private void fireElectionUpdatedEvent() {
		//All the listeners
		Iterator listeners = this.electionUpdatedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((ElectionUpdatedListener)listeners.next()).receiveElectionUpdatedEvent(new ElectionUpdatedEvent(this));
		}
	}
	
	public Race[] getRaceArray() {
			
		//Result array
		Race[] result = new Race[this.races.size()];
			
		//Populate result array
		for(int x=0; x<this.races.size(); x++) {
			result[x] = (Race)this.races.get(x);
		}
			
		//Return result array
		return result;

	}

}
