package uk.ac.surrey.pav.bulletinboard.challenges;

import java.io.Serializable;

/**
 * Stores the nonce together with the bitmap used to challenge the teller
 * 
 * @author David Lundin
 *
 */
public class NonceBitmapCouple implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public byte[] tellerNonce;
	
	public byte[] bitmap;
	
	public NonceBitmapCouple(byte[] tellerNonce, byte[] bitmap) {
		this.tellerNonce = tellerNonce;
		this.bitmap = bitmap;
	}
	
}
