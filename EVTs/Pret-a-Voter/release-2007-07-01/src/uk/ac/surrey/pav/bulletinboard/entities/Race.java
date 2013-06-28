package uk.ac.surrey.pav.bulletinboard.entities;

import java.util.ArrayList;
import java.util.Iterator;

import uk.ac.surrey.pav.ballotform.Permutation;
import uk.ac.surrey.pav.bulletinboard.challenges.Challenge;
import uk.ac.surrey.pav.bulletinboard.challenges.NonceBitmapCouple;
import uk.ac.surrey.pav.bulletinboard.events.RaceUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.RaceUpdatedListener;
import uk.ac.surrey.pav.bulletinboard.tally.Tally;


/**
 * A race is a position being contested
 * 
 * @author David Lundin
 *
 */
public class Race {

	/**
	 * The ID of the race (database primary key)
	 */
	public int raceID;
	
	/**
	 * Name of the race
	 */
	public String name;

	/**
	 * The candidates in this race
	 */
	public ArrayList candidates = new ArrayList();
	
	/**
	 * Parent election
	 */
	public Election election;
	
	/**
	 * A tally of this race
	 */
	public Tally tally = new Tally(this);
	
	/**
	 * A count of the ballot cast in this race
	 */
	public int ballotCount = 0;
	
	/**
	 * List of all the listeners for the RaceUpdatedEvent
	 */
	private ArrayList raceUpdatedListeners = new ArrayList();
	
	/**
	 * The batches during the tallying process
	 */
	public ArrayList batches = new ArrayList();
	
	/**
	 * Challenges contributed by the tellers (and perhaps others) to
	 * the audit of this race
	 */
	public ArrayList challenges = new ArrayList();

	/**
	 * Constructor
	 * 
	 * @param raceID	Primary key in the database
	 * @param name		Name of the race
	 */
	public Race(int ballotCount, Election election, int raceID, String name) {
		//Store details
		this.ballotCount = ballotCount;
		this.election = election;
		this.raceID = raceID;
		this.name = name;
	}
	
	/**
	 * Adds a candidate to the race
	 * 
	 * @param newCandidate Candidate object to add
	 */
	public void addCandidate(Candidate newCandidate) {
		this.candidates.add(newCandidate);
	}
	
	/**
	 * Returns a permutation in the canonical order for this race
	 * 
	 * @return Permutation object
	 */
	public Permutation getBaseOrderPermutation() {
		return new Permutation(this.candidates.size());
	}
	
	/**
	 * Increments the count of cast ballot forms by one 
	 *
	 */
	public void incrementBallotCount() {
		//Increment the number of ballots cast in the election
		this.election.incrementBallotCount();
		
		//Increment the number of ballots cast in this race
		this.ballotCount++;
	}
	
	/**
	 * Returns an array of Strings with all the candidate names
	 * in this election
	 * 
	 * @return An array of strings with the names of the candidates
	 */
	public String[] getCandidateNameList() {
		
		//A result
		String[] result = new String[this.candidates.size()];
		
		//Add all names
		for(int x=0; x<this.candidates.size(); x++) {
			result[x] = ((Candidate)this.candidates.get(x)).name;
		}
		
		//Done, return
		return result;
		
	}
	
	/**
	 * Adds a listener for the RaceUpdatedEvent
	 * 
	 * @param listener A listener to add
	 */
	public void addRaceUpdatedListener(RaceUpdatedListener listener) {
		this.raceUpdatedListeners.add(listener);
	}
	
	/**
	 * Removes a listener for the RaceUpdatedEvent
	 * 
	 * @param listener A listener to remove
	 */
	public void removeRaceUpdatedListener(RaceUpdatedListener listener) {
		this.raceUpdatedListeners.remove(listener);
	}
	
	/**
	 * Fire the RaceUpdatedEvent
	 *
	 */
	private void fireRaceUpdatedEvent() {

		//All the listeners
		Iterator listeners = this.raceUpdatedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((RaceUpdatedListener)listeners.next()).receiveRaceUpdatedEvent(new RaceUpdatedEvent(this));
		}
		
	}
	
	/**
	 * Returns the number of batches in the race if it is
	 * being audited
	 * 
	 * @return Number of batches
	 */
	public int getNumberOfBatches() {
		return this.batches.size();
	}
	
	/**
	 * Add a new batch to the list of batches
	 * 
	 * @param newBatch
	 */
	public void addBatch(Batch newBatch) {
		//Store the batch
		this.batches.add(newBatch);
		
		//Tell anyone who is listening
		this.fireRaceUpdatedEvent();
	}
	
	/**
	 * Returns the ID of the last teller
	 * 
	 * @return Integer of the ID of the last teller
	 */
	public int getLastBatchTellerID() {
		return ((Batch)this.batches.get(this.batches.size()-1)).tellerID;
	}
	
	/**
	 * Returns a batch by searching for a Teller ID
	 * 
	 * @param tellerID The teller for which to get a batch
	 * @return The batch for this teller
	 */
	public Batch getBatchFromTellerID(int tellerID) {
		
		for(int x=0; x<this.batches.size(); x++) {
			Batch currentBatch = (Batch)this.batches.get(x);
			if(currentBatch.tellerID == tellerID) {
				return currentBatch;
			}
		}
		return null;
		
	}
	
	/**
	 * Returns a challenge for a Teller ID
	 * 
	 * @param tellerID The teller for which to get the challenge
	 * @return The challenge for this teller
	 */
	public Challenge getChallengeFromTellerID(int tellerID) {

		for(int x=0; x<this.challenges.size(); x++) {
			Challenge currentChallenge = (Challenge)this.challenges.get(x);
			if(currentChallenge.tellerID == tellerID) {
				return currentChallenge;
			}
		}
		return null;

	}

	/**
	 * Store a challenge in the list
	 * 
	 * @param newChallenge
	 */
	public void addChallenge(Challenge newChallenge) {
		//Store the batch
		this.challenges.add(newChallenge);
		
		//Tell anyone who is listening
		this.fireRaceUpdatedEvent();
	}
	
	/**
	 * Update a challenge and fire the updated event
	 * 
	 * @param challenge
	 * @param newValue
	 */
	public void updateChallenge(Challenge challenge, NonceBitmapCouple newValue) {
		//Store the values
		challenge.setValue(newValue);
		
		//Tell anyone who is listening
		this.fireRaceUpdatedEvent();
	}

}
