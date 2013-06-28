package uk.ac.surrey.pav.ballotform;

import java.io.IOException;
import java.io.Serializable;
import java.security.InvalidKeyException;
import java.security.Key;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.util.Arrays;

import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.KeyGenerator;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;

import sun.misc.BASE64Encoder;

/**
 * Encapsulates the many layers of permutation
 * of the candidate list
 * 
 * @author David Lundin
 *
 */
public class Onion implements Serializable, Cloneable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * A cryptographically sealed object:
	 * simply containing an OnionLayer object which in turn
	 * contains an onion and a permutation.
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
	 * A hash of all the onion's layers
	 */
	public byte[] hash;
	
	/**
	 * This method adds a layer to the onion by creating a new OnionLayer
	 * object with the current onion and the permutation received
	 * as a parameter. This OnionLayer object is then sealed using RSA
	 * encryption with the public key received as a parameter
	 * and stored as the current onion.
	 * 
	 * @param rsaKey	The RSA public key of the teller that corresponds to this layer
	 * @param p			The permutation to add into this layer
	 */
	public void addLayer(PublicKey rsaKey, Permutation p) {

		//Create a new OnionLayer object
		OnionLayer newLayer;
		if(this.onion != null) {
			
			//There is already something in the onion
			//so create a new layer
			newLayer = new OnionLayer(this.onion, this.wrappedAesKey, p);
			
		} else {
			
			//This is the innermost layer of the onion
			//so create new layer
			newLayer = new OnionLayer(p);
			
		}

		//The hash has been created by the layer constructor
		//so simply store this here also
		this.hash = newLayer.hash;

		try {
			
			//Generate AES key
			KeyGenerator keyGen = KeyGenerator.getInstance("AES");
			keyGen.init(256); //Key length at maximum
			SecretKey tempAesKey = keyGen.generateKey();
			
			//Set up the AES cipher
			Cipher aesCipher = Cipher.getInstance("AES/ECB/PKCS5Padding");
			aesCipher.init(Cipher.ENCRYPT_MODE, tempAesKey);

			//Seal the newLayer object using AES
			this.onion = new CloneableSealedObject(newLayer, aesCipher);
			
			//Set up the RSA cipher
			Cipher rsaCipher = Cipher.getInstance("RSA");
			rsaCipher.init(Cipher.WRAP_MODE, rsaKey);
			
			//Wrap the aesKey object using RSA
			this.wrappedAesKey = rsaCipher.wrap(tempAesKey);
		
			//Print some testing info
			//System.out.println("Added a layer to the onion.");

		} catch (NoSuchPaddingException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (NoSuchAlgorithmException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (InvalidKeyException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (IllegalBlockSizeException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (IOException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		}

		//Print what has been added to the onion
		//System.out.println("Added layer: Permutation " + p.getString() + " Random " + newLayer.random);
	
	}
	
	/**
	 * This method takes a private key as parameter and uses it to unseal the
	 * OnionLayer object in this.onion. The permutation hidden underneath the
	 * layer is returned and the remaining onion stored as this.onion.
	 * 
	 * @param rsaKey	The private RSA key used to decrypt the top layer of the onion
	 * @return			The permutation hidden under the layer
	 */
	public OnionLayer removeLayer(PrivateKey rsaKey) throws InvalidKeyException {

		try {
			
			//Set up the RSA cipher
			Cipher rsaCipher = Cipher.getInstance("RSA");
			rsaCipher.init(Cipher.UNWRAP_MODE, rsaKey);

			//Unwrap the AES key
			Key tempAesKey =
				rsaCipher.unwrap(
					this.wrappedAesKey, 
					"AES", 
					Cipher.SECRET_KEY);
			
			//Unseal the onion object
			OnionLayer topLayer = (OnionLayer)this.onion.getObject(tempAesKey);
			
			//Store the new onion
			this.onion = topLayer.onion;
			
			//Store the new AES key
			this.wrappedAesKey = topLayer.wrappedAesKey;
			
			//Store the new hash
			this.hash = topLayer.hash;

			//Print what has been regained from the onion
			//System.out.println("Layer removed, got this: Permutation " + topLayer.permutation.getString() + " Random " + topLayer.random);

			//Return the permutation
			return topLayer;
			
		} catch (NoSuchPaddingException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
			return null;
		} catch (NoSuchAlgorithmException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
			return null;
		} catch (ClassNotFoundException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
			return null;
		} catch (IOException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
			return null;
		}

	}
	
	/**
	 * @return	a hash of the current onion
	 */
	public String getHashAsString() {

		//Encode the hash under Base64 and return as string
		BASE64Encoder encoder = new BASE64Encoder();
		return encoder.encode(this.hash);
		
	}
	
	/**
	 * Clones the Onion
	 * 
	 * @return A clone of the Onion
	 * @throws CloneNotSupportedException
	 */
	public Object clone() throws CloneNotSupportedException {
		
		//Clone the object with immutable fields
		Onion result = (Onion)super.clone();
		
		//Clone mutable fields
		result.onion = new CloneableSealedObject(this.onion);
		System.arraycopy(this.wrappedAesKey, 0, result.wrappedAesKey, 0, this.wrappedAesKey.length);
		
		//Done, return
		return result;
		
	}
	
	/**
	 * Compares two onions for the purpose of sorting them.
	 * Looks at the two hashes.
	 * 
	 * @param otherOnion The other onion
	 * @return An int representing the comparison between the two onions
	 */
	public int compareTo(Onion otherOnion) {
		
		//System.out.println("Comparing " + this.getHashAsString() + " to " + otherOnion.getHashAsString());
		
		if(Arrays.equals(this.hash, otherOnion.hash)) {
			
			//The two hashes are exactly the same!
			return 0;
			
		} else {
			
			for(int x = 0; x < this.hash.length && x < otherOnion.hash.length; x++) {
			
				if(this.hash[x] < otherOnion.hash[x]) {
					return -1;
				} else if(this.hash[x] > otherOnion.hash[x]) {
					return 1;
				}
				
			}
			
			//Turns out they are the same after all
			return 0;
			
		}
		
	}
	
}
