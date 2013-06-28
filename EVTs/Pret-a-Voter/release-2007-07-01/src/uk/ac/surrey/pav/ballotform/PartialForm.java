package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;
import java.security.InvalidKeyException;
import java.security.PrivateKey;

/**
 * This class is used when passing partially decrypted receipts
 * to and from tellers. It only contains an onion and a permutation.
 * 
 * @author David Lundin
 *
 */
public class PartialForm implements Serializable, Cloneable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The onion held in this partial form
	 */
	public Onion onion;
	
	/**
	 * The permutation holds the current representation of the voter's choices
	 */
	public CharacterPermutation permutation;
	
	/**
	 * The current choice that is the top one
	 */
	private int currentTopChoice = 0;
	
	/**
	 * When the form is discarded because it has no more
	 * choices to count then this is set to true
	 */
	private boolean discarded = false;
	
	/**
	 * Constructor
	 * 
	 * @param onion			An onion element from the original ballot form
	 * @param permutation	A permutation from the original ballot form
	 */
	public PartialForm(Onion onion, CharacterPermutation permutation) {
		//Store these
		this.onion = onion;
		this.permutation = permutation;
	}
	
	/**
	 * Clones the object
	 */
	public Object clone() throws CloneNotSupportedException {
		
		//Clone the object with immutable fields
		PartialForm result = (PartialForm)super.clone();
		
		//Clone mutable fields, namely this.onion and this.permutation
		result.onion = (Onion)this.onion.clone();
		result.permutation = (CharacterPermutation)this.permutation.clone();
		
		//Finished, return
		return result;
		
	}
	
	/**
	 * Removes a layer from the onion, permutes the permutation in
	 * this PartialForm, creates a TellerInternalBatchRow object and
	 * returns this.
	 * 
	 * @param rsaKey The private key used to remove the layer
	 * @return A batch row of the removed layer
	 * @throws InvalidKeyException
	 */
	public TellerInternalBatchRow removeLayerIntoRow(PrivateKey rsaKey) throws InvalidKeyException {
		
		//Remove the top layer of the onion
		OnionLayer topLayer = this.onion.removeLayer(rsaKey);
		
		//Apply the permutation in reverse order to the permutation here
		this.permutation.reverse(topLayer.permutation);
		
		//Return a new TellerInternalBatchRow
		return new TellerInternalBatchRow(new PartialForm(this.onion, this.permutation), topLayer.permutation, topLayer.random);
		
	}
	
	/**
	 * Moves to the next top choice and then returns true if this is possible
	 * or false if the form should be discarded because there are no choices
	 * left
	 * 
	 * @return True if the it was possible to find another top choice or false if the form should be discarded
	 */
	public boolean getNextTopChoice() {
		if(this.currentTopChoice < this.permutation.getNumberOfChoices() - 1) {
			//This form may be reassigned to another candidate pile
			this.currentTopChoice++;
			return true;
		} else {
			//This form has no more choices on it and so should be discarded
			this.discarded = true;
			return false;
		}
	}
	
	/**
	 * Return the current top choice
	 * 
	 * @return The current top choice index value
	 */
	public int getCurrentTopChoice() {
		System.out.println("Permutation: " + this.permutation.toString() + " Number of choices: " + this.permutation.getNumberOfChoices() + " Current top choice: " + this.currentTopChoice);
		return this.permutation.getCandidateInChoiceNumber(this.currentTopChoice);
	}
	
	/**
	 * Returns true if the form is still being counted and false
	 * if it has been discarded because no more choices exist
	 *  
	 * @return True if the ballot form is still in the count
	 */
	public boolean isStillInCount() {
		if(this.discarded == true || this.permutation.getNumberOfChoices() <= 0) {
			return false;
		} else {
			return true;
		}
	}
	
}
