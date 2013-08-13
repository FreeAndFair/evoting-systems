package votebox.crypto.interop;

import java.util.ArrayList;
import java.util.List;

import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.ElgamalCiphertext;
import edu.uconn.cse.adder.Polynomial;
import edu.uconn.cse.adder.PrivateKey;
import edu.uconn.cse.adder.PublicKey;

public class AdderKeyManipulator {
	private static PublicKey _cachedKey = null;
	private static Polynomial _poly = null;
	
	/**
	 * Sets the cached final public key.
	 * This is used so VoteBoxes and Supervisors can coordinate their
	 * key usage.
	 * 
	 * @param newKey - the key to load into the cache.
	 * @param baseKey - the key the newKey must be a derivative of.
	 */
	public static void setCachedKey(PublicKey newKey/*, PublicKey baseKey*/)/* throws AuditoriumCryptoException*/{
		/*if(baseKey.getF() != null && !(baseKey.getF().equals(newKey.getF())))
			throw new AuditoriumCryptoException("F's don't match", null);
		
		if(baseKey.getG() != null && !(baseKey.getG().equals(newKey.getG())))
			throw new AuditoriumCryptoException("G's don't match", null);
		
		if(baseKey.getP() != null && !(baseKey.getP().equals(newKey.getP())))
			throw new AuditoriumCryptoException("P's don't match", null);
		
		if(baseKey.getQ() != null && !(baseKey.getQ().equals(newKey.getQ())))
			throw new AuditoriumCryptoException("Q's don't match", null);
		
		if(baseKey.getH() != null && baseKey.getH().equals(newKey.getH()))
			throw new AuditoriumCryptoException("H's DO match", null);*/
		
		System.out.println("Cached Key Set: "+newKey);
		
		_cachedKey = newKey;
	}
	
	/**
	 * Generates the "final" public key using the pre-generated public key.
	 * This is needed for tallying and NIZK verification.
	 * This call returns the same key each time, but this key is different
	 * from run to run.
	 * 
	 * @param publicKey - the precalculated public key.
	 * @return the new PublicKey
	 */
	public static PublicKey generateFinalPublicKey(PublicKey publicKey){
		if(_cachedKey != null)
			return _cachedKey;
		
		_cachedKey = generateFinalPublicKeyNoCache(publicKey);
		
		return _cachedKey;
	}
	
	/**
	 * Generates the "final" public key using the pre-generated public key.
	 * This is needed to actually tally and perform NIZK verification.
	 * Additionally, this call will return a different variant of the public key
	 * every time it is called.
	 * 
	 * @param pubKey - the precalculated public key.
	 * @return the new PublicKey
	 */
	protected static PublicKey generateFinalPublicKeyNoCache(PublicKey pubKey){
		_poly = new Polynomial(pubKey.getP(), pubKey.getG(), pubKey.getF(), 0);
		
		AdderInteger p = pubKey.getP();
		AdderInteger q = pubKey.getQ();
		AdderInteger g = pubKey.getG();
		AdderInteger f = pubKey.getF();
		AdderInteger finalH = new AdderInteger(AdderInteger.ONE, p);
		
		AdderInteger gvalue = g.pow((_poly).
                evaluate(new AdderInteger(AdderInteger.ZERO, q)));
		finalH = finalH.multiply(gvalue);
		
		_cachedKey = new PublicKey(p, g, finalH, f);
		
		return _cachedKey;
	}
	
	/**
	 * Generates the "final" PrivateKey from the pre-generated one.
	 * This is needed to decrypt the totals calculated with the corresponding final public key.
	 * 
	 * @return the new PrivateKey
	 */
	public static PrivateKey generateFinalPrivateKey(PublicKey publicKey, PrivateKey privateKey){
		//Generate the final private key
		List<ElgamalCiphertext> ciphertexts = new ArrayList<ElgamalCiphertext>();
		ElgamalCiphertext ciphertext = publicKey.encryptPoly(_poly.evaluate(new AdderInteger(0, publicKey.getQ())));
		ciphertexts.add(ciphertext);
		PrivateKey finalPrivKey = privateKey.getFinalPrivKey(ciphertexts);
		
		return finalPrivKey;
	}	
}