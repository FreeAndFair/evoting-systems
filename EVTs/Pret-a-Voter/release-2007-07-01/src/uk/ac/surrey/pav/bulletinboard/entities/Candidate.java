package uk.ac.surrey.pav.bulletinboard.entities;

/**
 * A candidate is a person running for a position
 * 
 * @author David Lundin
 *
 */
public class Candidate {

	/**
	 * ID of the candidate in the database
	 */
	public int candidateID;
	
	/**
	 * The candidate's name
	 */
	public String name;

	/**
	 * Constructor
	 * 
	 * @param candidateID	Primary key in the database
	 * @param name			Name of the candidate
	 */
	public Candidate(int candidateID, String name) {
		//Store the details
		this.candidateID = candidateID;
		this.name = name;
	}
	
}
