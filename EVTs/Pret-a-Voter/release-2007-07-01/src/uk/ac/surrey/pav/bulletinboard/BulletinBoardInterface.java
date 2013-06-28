package uk.ac.surrey.pav.bulletinboard;

import java.rmi.Remote;
import java.rmi.RemoteException;

import uk.ac.surrey.pav.administrator.registry.Voter;
import uk.ac.surrey.pav.ballotform.Receipt;
import uk.ac.surrey.pav.ballotform.Vote;

/**
 * Remote interface for the bulletin board. Please see the BulletinBoardServer
 * object's methods for guidance.
 * 
 * @author David Lundin
 *
 */
public interface BulletinBoardInterface extends Remote {

	public Receipt postBallot(Vote vote) throws RemoteException;
	public Receipt auditForm(Vote vote) throws RemoteException;
	public Receipt cancelForm(Vote vote) throws RemoteException;
	public Voter voterLookup(String urn) throws RemoteException;
	public Voter assignFormToVoter(Voter voter, int serialNumber) throws RemoteException;
	public Voter cancelFormForVoter(Voter voter) throws RemoteException;
	public byte[] identifyTellerGetNonce(String tellerName) throws RemoteException;
	public boolean identifyTeller(String tellerName, String tellerServerName, String tellerServerAddress, byte[] signature) throws RemoteException;
	
}
