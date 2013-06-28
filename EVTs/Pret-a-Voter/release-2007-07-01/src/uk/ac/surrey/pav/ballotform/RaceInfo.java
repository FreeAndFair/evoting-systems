package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;

/**
 * Contains information about the election and race
 * for which this ballot form is valid.
 * 
 * @author David Lundin
 *
 */
public class RaceInfo implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Primary key of the election for which this form is valid.
	 */
	public int election;
	
	/**
	 * Primary key of the race in an election for which this form is valid.
	 */
	public int race;
	
	/**
	 * Creates the RaceInfo element.
	 * 
	 * @param election	The election for which this form is valid
	 * @param race		The race in the election for which this form is valid
	 */
	public RaceInfo(int election, int race) {
		//Store info about the election and race
		//These are simply primary keys in the database
		this.election = election;
		this.race = race;
	}
	
}
