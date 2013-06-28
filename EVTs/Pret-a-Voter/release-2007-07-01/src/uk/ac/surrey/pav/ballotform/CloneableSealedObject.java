package uk.ac.surrey.pav.ballotform;

import java.io.IOException;
import java.io.Serializable;

import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.SealedObject;

/**
 * Enxtends the SealedObject so that it can be cloned
 * 
 * @author David Lundin
 *
 */
public class CloneableSealedObject extends SealedObject {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor that simply passes the values on to the super constructor
	 * 
	 * @param object
	 * @param c
	 * @throws IOException 
	 * @throws IllegalBlockSizeException 
	 */
	public CloneableSealedObject(Serializable object, Cipher c) throws IllegalBlockSizeException, IOException {
		super(object, c);
	}
	
	/**
	 * Used to clone the object
	 * 
	 * @param object
	 */
	public CloneableSealedObject(CloneableSealedObject object) {
		super(object);
	}
	
	/**
	 * Clones the object
	 * 
	 * @return Cloned object
	 */
	public Object clone() {
		return new CloneableSealedObject(this);
	}
}
