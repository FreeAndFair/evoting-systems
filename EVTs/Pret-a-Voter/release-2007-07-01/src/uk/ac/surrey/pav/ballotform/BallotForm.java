package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;
import java.security.PrivateKey;
import java.security.PublicKey;

import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Holds a ballot form or an encrypted receipt.
 * 
 * @author David Lundin
 *
 */
public class BallotForm implements Serializable, SQLable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The serial number is printed on the ballot form
	 * and is used to perform a publicly verifiable translation
	 * between this shorter value and the much longer onion.
	 */
	public int serialNo;
	
	/**
	 * The candidate list is set if this is a
	 * complete pre-print ballot form. In all other cases
	 * this element will be null.
	 */
	public Permutation candidateList;
	
	/**
	 * The voting form contains the right-hand
	 * part of the ballot form.
	 */
	public VotingForm votingForm;
	
	/**
	 * The ballot form is available in the database
	 */
	public static String STATUS_AVAILABLE = "AVAILABLE";
	
	/**
	 * Sets up a blank ballot form.
	 * 
	 * @param serialNo		Serial number of the new ballot form
	 * @param candidates	The number of candidates in the race for which this is valid
	 * @param election		Primary key of the election for which this is valid
	 * @param race			A race in the election
	 */
	public BallotForm(int serialNo, int candidates, int election, int race) {
		//Hello world!
		//System.out.println("Hi, I'm a ballot form!");
		
		//Set the serial number
		this.serialNo = serialNo;
		
		//Set up the candidate list
		this.candidateList = new Permutation(candidates);
		
		//Set up the voting form
		this.votingForm = new VotingForm(election, race);
		
		//Print audit information
		//System.out.println("The candidate list is in the following order: " + this.candidateList.getString());
	}
	
	/**
	 * This method allows you to very simply add a permutation to the candidate
	 * list and hide it underneath a layer of the onion. Simply pass a public key
	 * and a random permutation is added for you.
	 * 
	 * @param key	A PublicKey of a teller
	 */
	public void addLayerToOnion(PublicKey key) {
		
		//Create a random permutation
		Permutation randomPermutation = new Permutation(this.candidateList.permutation.length, "Random");
		
		//Apply permutation to the permutation of the candidate list
		this.candidateList.permute(randomPermutation);
		
		//Add a layer to the onion
		this.votingForm.signedOnion.onion.addLayer(key, randomPermutation);

		//Print what the candidate list looks like right now
		//System.out.println("The candidate list is in the following order: " + this.candidateList.getString());
	}
	
	/**
	 * Removes a layer from the onion, performs the permutation of the voter's
	 * choices and then returns the layer for auditing purposes.
	 * 
	 * @param key	A private key used to decrypt the layer
	 * @return		The top layer for auditing purposes
	 */
	/*public OnionLayer removeLayerFromOnion(PrivateKey key) throws InvalidKeyException {
		
		//Get the top layer of the onion
		OnionLayer topLayer = this.votingForm.signedOnion.onion.removeLayer(key);
		
		//Perform the permutation to the voter's choice
		this.votingForm.vote.reverse(topLayer.permutation);

		//Print what the candidate list looks like right now
		//System.out.println("The voter choice is now set to: " + this.votingForm.vote.getString());

		//Return the top layer
		return topLayer;
		
	}*/
	
	/**
	 * Store the voter's choice on the ballot form.
	 * 
	 * @param p	A permutation describing the voter's choice
	 */
	public void setVote(CharacterPermutation p) {
		
		//Store this vote
		this.votingForm.vote = p;
		
		//Audit info printed
		//System.out.println("The voter choice is now set to: " + this.votingForm.vote.getString());
		
	}
	
	/**
	 * Signs the ballot form by passing the private key to the OnionRaceSignature object
	 * which signs those two objects
	 * 
	 * @param privateKey
	 */
	public void sign(PrivateKey privateKey) {
		this.votingForm.signedOnion.signature.sign(privateKey);
	}

	public StringBuffer toSQL() {

		//The result variable
		StringBuffer result = new StringBuffer();
		
		//Insert for the ballot form paper itself
		result.append("INSERT INTO ballotforms (ballotform_serialno, ballotform_status, election_id, race_id, ballotform_object) VALUES (");
		result.append(this.serialNo + ", ");
		result.append("'AVAILABLE', ");
		result.append(this.votingForm.signedOnion.raceInfo.election + ", ");
		result.append(this.votingForm.signedOnion.raceInfo.race + ", ");
		result.append("x'" + HexConstructor.serializeIntoHex(this) + "'");
		result.append(");");
		
		//Return
		return result;

	}

}
