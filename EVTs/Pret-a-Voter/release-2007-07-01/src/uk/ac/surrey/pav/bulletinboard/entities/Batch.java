package uk.ac.surrey.pav.bulletinboard.entities;

/**
 * Stores information about a batch in the audit process
 * 
 * @author David Lundin
 *
 */
public class Batch {

	/**
	 * The ID of the teller who has created this batch
	 */
	public int tellerID;
	
	/**
	 * The number of receipts in the two batches
	 */
	private int batchCount;
	
	/**
	 * Constructor
	 * 
	 * @param tellerID The ID of the teller that has created these batches
	 * @param batchCount The number of receipts in the batch
	 */
	public Batch(int tellerID, int batchCount) {
		//Store incoming
		this.tellerID = tellerID;
		this.batchCount = batchCount;
	}
}
