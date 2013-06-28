package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;

/**
 * This is used within the teller to perform the decryption
 * and shuffling of the batches. The TellerBatch object that is the
 * input batch is decrypted and the result, including the randomness
 * and the permutation, is stored in an ArrayList of these objects.
 * 
 * @author David Lundin
 *
 */
public class TellerInternalBatchRow implements Serializable, Comparable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The PartialForm that is the result of a layer removal
	 */
	public PartialForm partialForm;
	
	/**
	 * The permutation extracted from the OnionLayer and
	 * reversely applied to the voter's choice in the partialForm
	 */
	public Permutation permutation;
	
	/**
	 * The random extracted from the OnionLayer
	 */
	public byte[] random;
	
	/**
	 * If this TellerInternalBatchRow is number 3 in its batch and the
	 * sortIndex is 7 that means that the object in position 3 in the
	 * previous batch is sorted into position 7 in this batch. This object
	 * is thus actually in position 7 in this batch although it is stored
	 * in position 3.
	 */
	public int sortIndex;
	
	/**
	 * Constructor
	 * 
	 * @param partialForm
	 * @param permutation
	 * @param random
	 */
	public TellerInternalBatchRow(PartialForm partialForm, Permutation permutation, byte[] random) {
		
		//Store what is coming in
		this.partialForm = partialForm;
		this.permutation = permutation;
		this.random = random;
		
	}

	/**
	 * Sets the sort index value
	 * 
	 * @param sortIndex
	 */
	public void setSortIndex(int sortIndex) {
		
		this.sortIndex = sortIndex;

	}

	/**
	 * Compares two TellerInternalBatchRow objects, implemented
	 * for the purpose of sorting according to the onion
	 * 
	 * @param arg0 The object to compare this object to
	 * @return Integer value representing how the objects compare
	 */
	public int compareTo(Object arg0) {
		
		//Compare the .toString() of my onion to the .toString() of the other TellerInternalBatchRow object's onion
		return this.partialForm.onion.compareTo(((TellerInternalBatchRow)arg0).partialForm.onion);
		
	}
	
}
