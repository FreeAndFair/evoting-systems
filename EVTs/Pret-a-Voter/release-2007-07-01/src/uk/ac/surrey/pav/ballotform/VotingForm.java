package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;

/**
 * Contains the right-hand part of the ballot form
 * such as the onion and the representation of the
 * voter's choices.
 * 
 * @author David Lundin
 *
 */
public class VotingForm implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The status of the form is held here, for example:
	 * UNUSED    for a form that can be used to cast a vote
	 * CANCELLED when the process has been cancelled
	 * VOTED     when cast
	 * AUDITED   when audited during election phase
	 */
	public String status;
	
	/**
	 * If the BallotForm object that this VotingForm is
	 * a part of is used to represent an encrypted receipt
	 * then the voter's choice is held here.
	 */
	public CharacterPermutation vote;
	
	/**
	 * The onion that is associated with the voter's choice
	 * is held in a SignedOnion object.
	 */
	public SignedOnion signedOnion;
	
	/**
	 * Setting up a blank form.
	 * 
	 * @param election Election for which this form is valid
	 * @param race Race in an Election for which this form is valid
	 */
	public VotingForm(int election, int race) {
		//Create the empty vote
		this.vote = null;
		
		//Create the empty onion
		this.signedOnion = new SignedOnion(election, race);
	}
}
