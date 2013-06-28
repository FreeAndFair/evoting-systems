package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;

/**
 * Simply consists of an onion and a signature of the same
 * 
 * @author David Lundin
 *
 */
public class SignedOnion implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The onion
	 */
	public Onion onion;
	
	/**
	 * Information about the race for which
	 * this form is valid.
	 */
	public RaceInfo raceInfo;
	
	/**
	 * The signature
	 */
	public OnionRaceSignature signature;
	
	/**
	 * Used when setting up a blank ballot form
	 * 
	 * @param election	The election for which this form is valid
	 * @param race		The race in the election for which the form is valid
	 */
	public SignedOnion(int election, int race) {
		//Set up an empty onion
		this.onion = new Onion();
		
		//Information about the election and race
		this.raceInfo = new RaceInfo(election, race);
		
		//Empty signature
		this.signature = new OnionRaceSignature(this);
	}
}
