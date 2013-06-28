package uk.ac.surrey.pav.ballotform;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.Signature;
import java.security.SignatureException;
import java.util.ArrayList;

/**
 * The Vote object is created by the voting booth and is submitted to the web bulletin
 * board to submit votes in any number of races. Corresponds to a BallotFormPaper.
 * 
 * @author David Lundin
 *
 */
public class Vote implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The ID of the BallotFormPaper used to submit the vote
	 */
	public int id;
	
	/**
	 * The signed hash read in from the ballot form
	 */
	public byte[] signedHash;

	/**
	 * A list of Permutation objects that represents votes for all
	 * the constituent BallotForms
	 */
	public ArrayList permutations = new ArrayList();
	
	/**
	 * The ID number of the submitting booth
	 */
	public int boothID;
	
	/**
	 * A signature of all the objects in this vote by the booth
	 */
	private byte[] boothSignature;
	

	/**
	 * Constructor
	 * 
	 * @param id The ID of the vote
	 * @param signedHash The signed hash
	 * @param boothID The ID of the booth that submits the vote
	 */
	public Vote(int id, byte[] signedHash, int boothID) {
		
		//Store these
		this.id = id;
		this.signedHash = signedHash;
		this.boothID = boothID;
		
	}
	
	/**
	 * Allows you to add a vote in the next race (can only add them in
	 * strict order!) to this vote
	 * 
	 * @param vote An integer array representing the vote. You must specify all positions in the race and if a position is blank on the form please enter 0 in this position here.
	 */
	public void addVoteFromCharArray(char[] vote) {
		
		/*//New vote
		int[] newVote = new int[vote.length];
		
		//Translate each char to digit
		for(int x = 0; x < vote.length; x++) {
			
			//Translate
			switch(vote[x]) {
			
			//TODO: This should not be hardcoded to these characters!
			case '-':
				newVote[x] = 0;
				break;
			case 'x':
				newVote[x] = 1;
				break;
			case 'o':
				newVote[x] = 0;
				break;
			case '1':
				newVote[x] = 0;
				break;
			case '2':
				newVote[x] = 1;
				break;
			case '3':
				newVote[x] = 2;
				break;
				
			}
			
		}*/
		
		//Add a new permutation to the list
		this.permutations.add(new CharacterPermutation(vote));
		
	}
	
	/**
	 * Signs the Vote
	 *
	 */
	public void sign(PrivateKey privateKey) throws InvalidKeyException {
		
		try {
			
			//Create the signature object
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initSign(privateKey);
			
			//Add the signature
			signature.update(this.signedHash);
			
			//Add all the permutations
			for(int x = 0; x < this.permutations.size(); x++) {
			
		        //Serialize Onion
				ByteArrayOutputStream onionBAOS = new ByteArrayOutputStream() ;
		        ObjectOutput onionOO = new ObjectOutputStream(onionBAOS) ;
		        onionOO.writeObject((CharacterPermutation)this.permutations.get(x));
		        onionOO.close();
		        //Add to signature
		        signature.update(onionBAOS.toByteArray());
		        
			}
	        
	        //Sign and save
	        this.boothSignature = signature.sign();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NoSuchAlgorithmException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SignatureException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	/**
	 * Checks the booth signature
	 * 
	 * @param publicKey The public key used to check the signature
	 * @return True if the signature is correct
	 */
	public boolean checkSignature(PublicKey publicKey) throws InvalidKeyException {
		
		try {
			
			//Create the signature object
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initVerify(publicKey);
			
			//Add the signature
			signature.update(this.signedHash);
			
			//Add all the permutations
			for(int x = 0; x < this.permutations.size(); x++) {
			
		        //Serialize Onion
				ByteArrayOutputStream onionBAOS = new ByteArrayOutputStream() ;
		        ObjectOutput onionOO = new ObjectOutputStream(onionBAOS);
		        onionOO.writeObject((CharacterPermutation)this.permutations.get(x));
		        onionOO.close();
		        //Add to signature
		        signature.update(onionBAOS.toByteArray());
		        
			}
	        
	        //Sign and save
	        return signature.verify(this.boothSignature);
	        
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return false;
		} catch (NoSuchAlgorithmException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return false;
		} catch (SignatureException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return false;
		}

	}

}
