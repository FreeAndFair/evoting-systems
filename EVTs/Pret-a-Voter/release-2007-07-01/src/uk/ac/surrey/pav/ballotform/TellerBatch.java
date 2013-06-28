package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;
import java.util.ArrayList;

/**
 * The teller batch class is used to pass batches of partially
 * decrypted receipts to and from tellers. It is very similar to the Batch
 * class but only holds and onion and the current permutation of the
 * voter's choice(s).
 * 
 * @author David Lundin
 *
 */
public class TellerBatch implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The signature on the Batch object allows
	 * any entity that passes a batch to another
	 * to sign that batch.
	 */
	public String signature;
	
	/**
	 * This method returns a hash of all the ballot forms
	 * in the batch so that the whole batch may be signed.
	 */
	public String getBatchHash() {
		//TODO: Implement this method
		return "";
	}
	
	/**
	 * The full batch of ballot forms is held
	 * in this array.
	 * 
	 * TODO: Check the maximum length of this array and consider other structure
	 */
	public ArrayList ballotForms;
	
	/**
	 * Add a ballot form to the batch
	 * @param ballotForm	The ballot form to add to the batch
	 */
	public void addBallotForm(PartialForm ballotForm) {
		
		ballotForms.add(ballotForm);
		
	}
	
	/**
	 * Constructor
	 */
	public TellerBatch() {
		
		//Create an empty list of partial ballot forms
		this.ballotForms = new ArrayList();
		
	}
	
}
