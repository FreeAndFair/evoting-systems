package uk.ac.surrey.pav.ballotform;

import java.io.ByteArrayOutputStream;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.interfaces.RSAPrivateKey;
import java.security.interfaces.RSAPublicKey;
import java.util.ArrayList;

import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.CSVable;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * Contains a number of ballot forms, one for each race in an election,
 * that are printed onto the same paper.
 * 
 * @author David Lundin (and Joson Xia)
 *
 */
public class BallotFormPaper implements Serializable, CSVable, SQLable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 7480093999307056534L;
	
	/**
	 * The ballot forms printed onto this paper
	 */
	private ArrayList forms;
	
	/**
	 * A signature of the hash
	 */
	public byte[] signedHash;
	
	/**
	 * The hash of the SignedOnions in the constituent BallotForms
	 */
	private byte[] hash;
	
	/**
	 * The ID of this BallotFormPaper
	 */
	private int id;

	/**
	 * Constructor
	 * 
	 * @param id
	 */
	public BallotFormPaper(int id) {
		forms = new ArrayList();
		this.id = id;
	}

	/**
	 * Creates and stores a hash of the constituent SignedOnions
	 *
	 */
	public void hash() {
		try {
			
			//A message hash
			MessageDigest md = MessageDigest.getInstance("MD5");
			
			//For each ballot form
			for(int x = 0; x < this.forms.size(); x++) {

				//... serialise the SignedOnion into a byte array
				ByteArrayOutputStream BAOS = new ByteArrayOutputStream();
				ObjectOutput OO = new ObjectOutputStream(BAOS);
				OO.writeObject(((BallotForm)this.forms.get(x)).votingForm.signedOnion);
				OO.close();

				//Update the hash with the SignedOnion
				md.update(BAOS.toByteArray());

			}
			
			
			//Store the hash
			this.hash = md.digest();

		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	/**
	 * Creates the hash and then signs it
	 * 
	 * @param privateKey
	 */
	public void signHash(PrivateKey privateKey) {
		
		//Start by updating the hash
		this.hash();

		//Sign and store this signature
		this.signedHash = addHashSignature(this.hash, privateKey);

	}
	
	/**
	 * Removes the signature and returns the hash
	 * 
	 * @param signedHash The signed hash
	 * @param publicKey The public key
	 * @return The hash with the signature removed
	 */
	public static byte[] removeHashSignature(byte[] signedHash, PublicKey publicKey) {
		
		//Remove the signature and return the hash
		BigInteger bigInt = new BigInteger(1, signedHash);
		int length = 16; //The hash should be 32 bytes long
		byte[] temp = bigInt.modPow(((RSAPublicKey)publicKey).getPublicExponent(), ((RSAPublicKey)publicKey).getModulus()).toByteArray();
		byte[] result = new byte[length];
		for(int x = 0; x < length; x++) {
			result[x] = (byte)0;
		}
		int lengthDifference = length - temp.length;
		if(lengthDifference >= 0) {
			//We want to pad out
			for(int x = 0; x < temp.length; x++) {
				result[x + lengthDifference] = temp[x];
			}
		} else {
			//We want to remove
			for(int x = 0; x < result.length; x++) {
				result[x] = temp[x - lengthDifference];
			}
		}
		return result;
		
	}
	
	/**
	 * Adds a signature and returns the signed hash
	 * 
	 * @param hash The hash to sign
	 * @param privateKey The private key to use to sign the hash
	 * @return The signed hash
	 */
	public static byte[] addHashSignature(byte[] hash, PrivateKey privateKey) {
		
		//Add signature and return signed hash
		BigInteger bigInt = new BigInteger(1, hash);
		int length = 128; //The hash should be 32 bytes long
		byte[] temp = bigInt.modPow(((RSAPrivateKey)privateKey).getPrivateExponent(), ((RSAPrivateKey)privateKey).getModulus()).toByteArray();
		byte[] result = new byte[length];
		for(int x = 0; x < length; x++) {
			result[x] = (byte)0;
		}
		int lengthDifference = length - temp.length;
		if(lengthDifference >= 0) {
			//We want to pad out
			for(int x = 0; x < temp.length; x++) {
				result[x + lengthDifference] = temp[x];
			}
		} else {
			//We want to remove
			for(int x = 0; x < result.length; x++) {
				result[x] = temp[x - lengthDifference];
			}
		}
		return result;
		
	}

	/**
	 * Adds a form to the list
	 * 
	 * @param f
	 */
	public void addForm(BallotForm f) {
		this.forms.add(f);
	}

	/**
	 * Gets a form from the list
	 * 
	 * @param k The index number of the form to get
	 * @return The ballot form
	 */
	public BallotForm getForm(int k) {
		return (BallotForm)this.forms.get(k);
	}

	/**
	 * Returns the comma separated value list of this BallotFormPaper object
	 * 
	 * @return Comma separated value list of the object
	 */
	public StringBuffer toCSV() {
		
		//The CSV to be returned
		StringBuffer result = new StringBuffer();
		
		//The responseCode, i.e. saying this is a ballot form to print
		result.append(Receipt.BALLOT_FORM_TO_BE_PRINTED);
		result.append(",");

		//The ID of the BallotFormPaper
		result.append(this.id);
		result.append(",");

		//The signed hash
		String signedHash = HexConstructor.byteArrayToHexString(this.signedHash);
		result.append(signedHash);
		result.append(",");
		
		//The hash
		String hash = HexConstructor.byteArrayToHexString(this.hash);
		result.append(hash);
		result.append(",");

		//The signed hash again
		result.append(signedHash);
		result.append(",");

		//The number of races
		result.append(this.forms.size());
		result.append(",");
		
		//For each ballot form that I have...
		for(int x=0; x<this.forms.size(); x++) {
		
			//...add its permutation
			result.append(((BallotForm)this.forms.get(x)).candidateList.getPermutationStringIncrementedByOne());
			
			//No trailing comma
			if(x < this.forms.size() - 1) {
				result.append(",");
			}	
			 
		}
		 
		result.append("\n");
		
		//Done, return the CSV string
		return result;
	}

	/**
	 * Returns the SQL of this ballot form paper for the purpose
	 * of inserting into a database
	 */
	public StringBuffer toSQL() {

		//The result variable
		StringBuffer result = new StringBuffer();

		//Pretty print the hash
		String temp = HexConstructor.byteArrayToHexString(this.hash);
		BigInteger h = new BigInteger("00" + temp, 16);
		String hashString = h.toString(32);
		while (hashString.length() < 26) hashString = "0" + hashString;
		String hashPrettyString = hashString.substring(0, 5) + "-"
				+ hashString.substring(5, 10) + "-"
				+ hashString.substring(10, 13) + "\\\\"
				+ hashString.substring(13, 18) + "-"
				+ hashString.substring(18, 23) + "-"
				+ hashString.substring(23, 26);
		
		//Insert for the ballot form paper itself
		result.append("INSERT INTO ballotformpapers (ballotformpaper_id, ballotformpaper_hash, ballotformpaper_plaintext_hash, ballotformpaper_status) VALUES (");
		result.append(this.id + ", ");
		result.append("x'" + HexConstructor.serializeIntoHex(this.hash) + "', ");
		result.append("'" + hashPrettyString + "', ");
		result.append("'AVAILABLE'");
		result.append(");\n");
		
		//And now for all its children
		for(int x = 0; x < this.forms.size(); x++) {
			
			//The ballot form
			result.append(((BallotForm)this.forms.get(x)).toSQL());
			result.append("\n");
			
			//Connector between paper and form
			result.append("INSERT INTO ballotformsinpapers (ballotformpaper_id, ballotform_id, position) VALUES (");
			result.append(this.id + ", ");
			result.append(((BallotForm)this.forms.get(x)).serialNo + ", ");
			result.append(x);
			result.append(");\n");
			
		}
		
		//Okay done, return
		return result;

	}
}

