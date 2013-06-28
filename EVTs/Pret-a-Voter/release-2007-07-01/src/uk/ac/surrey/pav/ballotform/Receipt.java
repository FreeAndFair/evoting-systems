package uk.ac.surrey.pav.ballotform;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
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

import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.CSVable;

/**
 * The Receipt is returned by the web bulletin board as a response
 * to the posting of a Vote
 * 
 * @author David Lundin
 *
 */
public class Receipt implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * A response code
	 */
	public int responseCode;
	
	/**
	 * This is a receipt for a correctly posted vote
	 */
	public static final int CORRECTLY_POSTED_RECEIPT = 31;
	
	/**
	 * This is a receipt for an audit request
	 */
	public static final int AUDIT_RECEIPT = 32;
	
	/**
	 * This is a ballot form that is going to be printed
	 */
	public static final int BALLOT_FORM_TO_BE_PRINTED = 30;
	
	/**
	 * This is a remote ballot form to be printed
	 */
	public static final int REMOTE_BALLOT_FORM_TO_BE_PRINTED = 33;
	
	/**
	 * The poster is not a valid booth
	 */
	public static final int ERROR_NOT_A_BOOTH = 41;
	
	/**
	 * There was a problem with the database on the web bulletin board
	 */
	public static final int ERROR_DATABASE_PROBLEM = 42;
	
	/**
	 * The ballot form was invalid or did not correspond to the ballot form in the database
	 */
	public static final int ERROR_INVALID_BALLOT_FORM = 43;
	
	/**
	 * There was a different internal bulletin board problem
	 */
	public static final int ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM = 44;
	
	/**
	 * A teller was down when an audit was attempted
	 */
	public static final int ERROR_TELLER_DOWN = 45;
	
	/**
	 * The ballot form has already been used
	 */
	public static final int ERROR_BALLOT_FORM_USED = 46;
	
	/**
	 * The hash check failed
	 */
	public static final int ERROR_INVALID_HASH = 47;
	
	/**
	 * The ballot form casting the vote is malformed
	 */
	public static final int ERROR_VOTE_MALFORMED = 48;
	
	/**
	 * A scanning problem
	 */
	public static final int ERROR_SCANNING_PROBLEM = 49;
	
	/**
	 * The ID number of the ballot for which this is a receipt
	 */
	private int ballotID;
	
	/**
	 * Signature of the producer of the receipt
	 */
	private byte[] signature;
	
	/**
	 * Permutations may be a set of votes
	 */
	private ArrayList permutations = null;
	
	/**
	 * An optional message
	 */
	private String message;
	
	/**
	 * The hash of the ballot form
	 */
	private byte[] hash;
	
	/**
	 * The ballot form hash signed by the administrator
	 */
	private byte[] signedHash;

	/**
	 * Constructor
	 * 
	 * @param errorCode The error code
	 * @param ballotID Ballot form serial number
	 * @param hash The hash on the form
	 * @param signedHash The signed hash
	 * @param permutations The permutations in the receipt
	 * @param message Any message that should be printed no the receipt
	 * @param privateKey The private key used to sign the receipt
	 */
	public Receipt(int errorCode, int ballotID, byte[] hash, byte[] signedHash, ArrayList permutations, String message, PrivateKey privateKey) {
		
		//Store the bits
		this.responseCode = errorCode;
		this.ballotID = ballotID;
		this.hash = hash;
		this.signedHash = signedHash;
		this.permutations = permutations;
		this.message = message;

		//Sign
		try {
			this.sign(privateKey);
		} catch (InvalidKeyException e) {
			e.printStackTrace();
		}

	}

	/**
	 * This is a receipt but has not got a list of choices because it is the result of
	 * an audit that failed.
	 * 
	 * @param errorCode
	 * @param ballotID
	 * @param hash
	 * @param signedHash
	 * @param message
	 * @param privateKey
	 */
	public Receipt(int errorCode, int ballotID, byte[] hash, byte[] signedHash, String message, PrivateKey privateKey) {
		
		//Store the other bits
		this.responseCode = errorCode;
		this.ballotID = ballotID;
		this.hash = hash;
		this.signedHash = signedHash;
		this.message = message;

		//Sign
		try {
			this.sign(privateKey);
		} catch (InvalidKeyException e) {
			e.printStackTrace();
		}

	}

	/**
	 * This constructor is used when a set of permutations are involved,
	 * for example when this is a receipt for a successfully posted vote
	 * 
	 * @param permutations
	 * @throws InvalidKeyException 
	 */
	public Receipt(int type, int ballotID, byte[] hash, byte[] signedHash, ArrayList permutations, PrivateKey privateKey) {
		
		//Store
		this.responseCode = type;
		this.ballotID = ballotID;
		this.hash = hash;
		this.signedHash = signedHash;
		this.permutations = permutations;
		
		//Sign
		try {
			this.sign(privateKey);
		} catch (InvalidKeyException e) {
			e.printStackTrace();
		}
		
	}
	
	/**
	 * Sign the receipt
	 * 
	 * @param privateKey
	 */
	private void sign(PrivateKey privateKey) throws InvalidKeyException {

		try {
			
			//Create the signature object
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initSign(privateKey);
			
			//Add the ballot ID
			ByteArrayOutputStream bos = new ByteArrayOutputStream();
			DataOutputStream dos = new DataOutputStream(bos);
			dos.writeInt(this.ballotID);
			dos.flush();
			signature.update(bos.toByteArray());
			
			//Add all the permutations
			if(this.permutations != null) {

				for(int x = 0; x < this.permutations.size(); x++) {
					
			        //Serialize Onion
					ByteArrayOutputStream onionBAOS = new ByteArrayOutputStream() ;
			        ObjectOutput onionOO = new ObjectOutputStream(onionBAOS) ;
			        onionOO.writeObject(this.permutations.get(x));
			        onionOO.close();
			        //Add to signature
			        signature.update(onionBAOS.toByteArray());
			        
				}

			}
	        
	        //Sign and save
	        this.signature = signature.sign();

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
	 * Check the signature
	 * 
	 * @param publicKey The public key used to check the signature
	 * @return True if the signature is correct
	 */
	public boolean checkSignature(PublicKey publicKey) {

		try {
			
			//Create the signature object
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initVerify(publicKey);
			
			//Add the ballot ID
			ByteArrayOutputStream bos = new ByteArrayOutputStream();
			DataOutputStream dos = new DataOutputStream(bos);
			dos.writeInt(this.ballotID);
			dos.flush();
			signature.update(bos.toByteArray());
			
			//Add all the permutations
			if(this.permutations != null) {
	
				for(int x = 0; x < this.permutations.size(); x++) {
					
			        //Serialize Onion
					ByteArrayOutputStream onionBAOS = new ByteArrayOutputStream() ;
			        ObjectOutput onionOO = new ObjectOutputStream(onionBAOS) ;
			        onionOO.writeObject(this.permutations.get(x));
			        onionOO.close();
			        //Add to signature
			        signature.update(onionBAOS.toByteArray());
			        
				}
	
			}
	        
	        //Sign and save
	        return(signature.verify(this.signature));

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
		} catch (InvalidKeyException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return false;
		}

	}
	
	/**
	 * Returns a String with a HTML representation of the receipt.
	 * 
	 * @return HTML of the receipt
	 */
	public String toHTML() {
		
		//What we are returning
		StringBuffer result = new StringBuffer();
		
		//Start the HTML
		result.append("<html><body>");
		
		//TODO: Add receipt here
		result.append("<h1>THIS IS A RECEIPT!!</h1>");
		
		//If there is a message
		if(this.message != null) {
			result.append("Message: " + message);
		}
		
		//End the HTML
		result.append("</body></html>");
		
		//Done, return
		return result.toString();
		
	}
	
	/**
	 * Returns comma separated values of the receipt to use in an external printing procedure
	 * 
	 * @return CSV of the receipt
	 */
	public String toCSV() {
		
		//System.out.println("Message: " + this.message);
		
		//The result
		StringBuffer result = new StringBuffer();
		
		//Response code
		result.append(this.responseCode + ",");

		//Serial no
		result.append(this.ballotID + ",");
		
		//Signed hash
		result.append(HexConstructor.byteArrayToHexString(this.signedHash) + ",");
		
		//Hash
		result.append(HexConstructor.byteArrayToHexString(this.hash) + ",");

		//Signature
		result.append(HexConstructor.byteArrayToHexString(this.signature) + ",");
		
		//Check if there are any permutations
		if(this.permutations != null) {

			//The number of races
			result.append(this.permutations.size() + ",");

			//Add all the permutations
			for(int x = 0; x < this.permutations.size(); x++) {
				
				//Add this permutation
				result.append(((CSVable)this.permutations.get(x)).toCSV());

				//If this is not the last permutation then add a comma
				if(x < this.permutations.size() - 1) {
					result.append(",");
				}
				
			}

		} else {

			//There are no races so append 0
			result.append("0,");

		}
		
		//Return
		return result.toString();
		
	}
	
	/**
	 * Translates a Permutation object to a String with special
	 * regard to the formatting required when the receipt is printed.
	 * 
	 * @param permutation
	 * @return
	 */
	/*public static String permutationToReceiptString(Permutation permutation, int language, int receiptType) {
		
		//This is what we are going to return
		StringBuffer result = new StringBuffer();
		
		//Go through the permutation
		for(int x = 0; x < permutation.permutation.length; x++) {
			
			//The current digit
			int currentDigit = permutation.permutation[x];
			
			//Change what symbols we are setting out as
			if(language == 0 || receiptType == Receipt.AUDIT_RECEIPT) {
				
				//TODO: This is a hack
				currentDigit++;
				
				if(currentDigit == 0) {
					result.append("-");
				} else {
					//Append the digit
					result.append(currentDigit);
				}
				
			} else {
				
				//Append a x or o
				if(currentDigit == 1) {
					result.append("x");
				} else {
					result.append("o");
				}
				
			}

		}
		
		//Finished, return
		return result.toString();
		
	}*/
	
}
