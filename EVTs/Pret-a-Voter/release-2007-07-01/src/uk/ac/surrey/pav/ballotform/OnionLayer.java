package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Random;


/**
 * This stores an onion and a permutation which is then
 * encrypted into the onion.
 * 
 * @author David Lundin
 *
 */
public class OnionLayer implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The onion at this layer, a SealedObject
	 * containing an OnionLayer
	 */
	public CloneableSealedObject onion;

	/**
	 * As the onion grows it becomes impossible to encrypt
	 * using RSA. Therefore the onion itself is encrypted using
	 * AES and the AES key of the underlying layer is stored
	 * in the onion and in each layer in the aesKey variable.
	 */
	public byte[] wrappedAesKey;

	/**
	 * The permutation under this layer
	 */
	public Permutation permutation;

	/**
	 * A random seed used foil brute force attacks
	 */
	public byte[] random;
	
	/**
	 * A hash of all the underlying layers
	 */
	public byte[] hash;
	
	/**
	 * When this is the innermost layer of the onion,
	 * simply encapsulating a permutation
	 * 
	 * @param permutation	The permutation to hide under this layer
	 */
	public OnionLayer(Permutation permutation) {
		
		//Simply store the permutation
		this.permutation = permutation;
		
		//Add the randomness
		Random rnd = new Random();
		this.random = new byte[16];
		rnd.nextBytes(this.random);
		
		//Hash the layer
		this.createHash();
		
	}
	
	/**
	 * When this layer is not the innermost.
	 * 
	 * @param onion			The onion as it looked at the previous layer
	 * @param wrappedAesKey	The key used to seal the onion, wrapped in RSA
	 * @param permutation	The permutation to hide under this layer
	 */
	public OnionLayer(CloneableSealedObject onion, byte[] wrappedAesKey, Permutation permutation) {
		
		//Simply store incoming variables
		this.onion = onion;
		this.wrappedAesKey = wrappedAesKey;
		this.permutation = permutation;

		//Add the randomness
		Random rnd = new Random();
		this.random = new byte[16];
		rnd.nextBytes(this.random);

		//Hash the layer
		this.createHash();

	}
	
	/**
	 * Hashes the onionlayer, called by the constructors
	 *
	 */
	private void createHash() {
		
		try {
			
			//Create a digest
			MessageDigest md = MessageDigest.getInstance("SHA1");
			
			//Update digest with permutation
			md.update(this.permutation.getBytes());
			
			//Update digest with randomness
			md.update(this.random);
			
			//Store digest
			this.hash = md.digest();
			
		} catch (NoSuchAlgorithmException e) {
			
			//TODO: Deal with this error here
			e.printStackTrace();
			
		}

	}
	
}
