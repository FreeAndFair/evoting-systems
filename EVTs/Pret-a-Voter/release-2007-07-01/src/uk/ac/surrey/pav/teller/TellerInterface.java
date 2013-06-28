package uk.ac.surrey.pav.teller;

import java.math.BigInteger;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.security.InvalidKeyException;
import java.util.ArrayList;

import uk.ac.surrey.pav.ballotform.Onion;
import uk.ac.surrey.pav.ballotform.TellerBatch;
import uk.ac.surrey.pav.bulletinboard.challenges.LeftRightGerm;
import uk.ac.surrey.pav.bulletinboard.challenges.NonceBitmapCouple;

/**
 * This is the interface with the Teller module used with RMI.
 * 
 * @author David Lundin
 *
 */
public interface TellerInterface extends Remote {

	/**
	 * The Teller receives an onion and is charged by the web bulletin board
	 * to remove its two layers of encryption and return an ArrayList containing
	 * (Permutation, onion, Permutation, onion).
	 * 
	 * @param onion	An Onion to peel two layers off
	 * @return		An ArrayList element containing (Permutation, onion, Permutation, onion) elements
	 * @throws RemoteException
	 */
	public ArrayList reveal(Onion onion) throws RemoteException, InvalidKeyException;
	
	/**
	 * This is used during the post-election phase when the election is audited
	 * and the mask is a map of all the connections between the two batches
	 * that the Teller has in memory. The teller returns an integer array which
	 * reveals the desired mappings.
	 * 
	 * @param mask	A BigInteger containing a binary number with the same size as the TellerBatch previously passed
	 * @return		A two-dimensional integer array which corresponds to the revealed links
	 * @throws RemoteException
	 */
	public ArrayList audit(int election, int race, int BatchID, BigInteger mask) throws RemoteException;
	
	/**
	 * The web bulletin board submits to the teller a list of partially decrypted
	 * receipts and it returns an ArrayList of two such batches after decryption
	 * and shuffling.
	 * 
	 * @param batch	A TellerBatch object containing the partially decrypted receipts
	 * @return		An ArrayList of two TellerBatches
	 * @throws RemoteException
	 */
	public ArrayList processVote(int election, int race, int batchID, TellerBatch batch) throws RemoteException, InvalidKeyException;
	
	public byte[] getCommitment(int election, int race, byte[] random) throws RemoteException;
	
	public NonceBitmapCouple getValue(int election, int race) throws RemoteException;
	
	public byte[] handShake(byte[] nonce) throws RemoteException;
	
}
