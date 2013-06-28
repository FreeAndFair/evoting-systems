package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;
import java.util.ArrayList;

/**
 * The Batch is a class simply to organise a number of ballot forms.
 * These ballot forms are communicated from one entity to another
 * and actions are performed on the batch as a whole.
 * 
 * @author David Lundin
 *
 */
public class Batch implements Serializable {

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
	 * Allows a batch to be identified by any entity that
	 * creates the object.
	 */
	public int batchID;
	
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
	public void addBallotForm(BallotForm ballotForm) {
		ballotForms.add(ballotForm);
	}
	
	public Batch() {
		//Create an empty list of ballot forms
		this.ballotForms = new ArrayList();
	}
}
