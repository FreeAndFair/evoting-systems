package uk.ac.surrey.pav.bulletinboard.tally;

/**
 * Stores information about one round of the tally
 * 
 * @author David Lundin
 *
 */
public class TallyRound {

	/**
	 * Human readable name of the round, i.e. Round 1
	 */
	public String name;
	
	/**
	 * The scores for each candidate at this stage 
	 */
	public int[] scores;
	
	/**
	 * The number of discarded forms
	 */
	public int discarded;

	/**
	 * A description of the round in human readable form
	 */
	public String description;
	
	/**
	 * Constructor
	 * 
	 * @param name
	 * @param scores
	 * @param description
	 */
	public TallyRound(String name, int[] scores, int discarded, String description) {
		//Simply store these immutable values
		this.name = name;
		this.scores = new int[scores.length];
		System.arraycopy(scores, 0, this.scores, 0, scores.length);
		this.discarded = discarded;
		this.description = description;
		
		//Print some stuff
		System.out.println("Name: " + name + ", scores: " + scores.length + " fields, desc: " + description);
	}
	
}
