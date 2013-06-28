package uk.ac.surrey.pav.bulletinboard.challenges;

/**
 * This class is used to store the challenges got from the tellers
 * 
 * @author David Lundin
 *
 */
public class Challenge {

	public int tellerID;
	
	public byte[] bulletinBoardNonce;
	
	public byte[] commitment;
	
	public byte[] tellerNonce;
	
	public byte[] bitmap;
	
	public Challenge(int tellerID, byte[] commitment, byte[] bulletinBoardNonce) {
		this.tellerID = tellerID;
		this.commitment = commitment;
		this.bulletinBoardNonce = bulletinBoardNonce;
	}
	
	public void setValue(NonceBitmapCouple bitmapCouple) {
		this.tellerNonce = bitmapCouple.tellerNonce;
		this.bitmap = bitmapCouple.bitmap;
	}
	
	public Challenge(int tellerID, byte[] bulletinBoardNonce, byte[] commitment, byte[] tellerNonce, byte[] bitmap) {
		this.tellerID = tellerID;
		this.bulletinBoardNonce = bulletinBoardNonce;
		this.commitment = commitment;
		this.tellerNonce = tellerNonce;
		this.bitmap = bitmap;
	}
	
}
