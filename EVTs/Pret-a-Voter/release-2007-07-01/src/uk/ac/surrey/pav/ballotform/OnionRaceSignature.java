package uk.ac.surrey.pav.ballotform;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.Signature;
import java.security.SignatureException;

/**
 * Is part of the SignedOnion and simply stores a signed hash of
 * the Onion and RaceInfo objects.
 * 
 * @author David Lundin
 *
 */
public class OnionRaceSignature implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This is a signed serialization of the Onion and RaceInfo objects.
	 */
	public byte[] signedOnionRaceInfo;
	
	/**
	 * Holds a reference to the parent SignedOnion
	 */
	private SignedOnion parentSignedOnion;

	/**
	 * This constructor stores a reference to the parent SignedOnion
	 * object for the purpose of calculating hashes of the Onion and
	 * RaceInfo objects at a later time.
	 * 
	 * @param signedOnion	The SignedOnion object that references this.
	 */
	public OnionRaceSignature(SignedOnion signedOnion) {
		//Simply store
		this.parentSignedOnion = signedOnion;
	}
	
	/**
	 * Creates a hash of the Onion and RaceInfo objects
	 * of type MessageDigest and seales this into the hash
	 * variable. THIS METHOD IS INCOMPLETE
	 * 
	 * @param rsaKey	A RSA private key of the signer
	 */
	public void sign(PrivateKey rsaKey) {
		try {
			
			//Create the signature object
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initSign(rsaKey);

	        //Serialize Onion
			ByteArrayOutputStream onionBAOS = new ByteArrayOutputStream() ;
	        ObjectOutput onionOO = new ObjectOutputStream(onionBAOS) ;
	        onionOO.writeObject(this.parentSignedOnion.onion);
	        onionOO.close();
	        //Add to signature
	        signature.update(onionBAOS.toByteArray());
	        
	        //Serialize RaceInfo
			ByteArrayOutputStream raceInfoBAOS = new ByteArrayOutputStream();
	        ObjectOutput raceInfoOO = new ObjectOutputStream(raceInfoBAOS);
	        raceInfoOO.writeObject(this.parentSignedOnion.raceInfo);
	        raceInfoOO.close();
	        //Add to signature
	        signature.update(raceInfoBAOS.toByteArray());

	        //Sign and save
	        this.signedOnionRaceInfo = signature.sign();
	        
		} catch (IOException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (InvalidKeyException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (SignatureException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		} catch (NoSuchAlgorithmException e) {
			//TODO: Deal with this exception
			e.printStackTrace();
		}
	}
}
