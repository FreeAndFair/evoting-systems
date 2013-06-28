package uk.ac.surrey.pav.bulletinboard.entities;

import java.math.BigInteger;
import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.PublicKey;
import java.security.Signature;
import java.security.SignatureException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Random;

import uk.ac.surrey.pav.ballotform.Onion;
import uk.ac.surrey.pav.ballotform.TellerBatch;
import uk.ac.surrey.pav.bulletinboard.TellerConnectorThread;
import uk.ac.surrey.pav.bulletinboard.challenges.NonceBitmapCouple;
import uk.ac.surrey.pav.bulletinboard.events.TellerUpdatedEvent;
import uk.ac.surrey.pav.bulletinboard.events.TellerUpdatedListener;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerDownException;
import uk.ac.surrey.pav.teller.TellerInterface;

/**
 * Keeps information about the teller that the bulletin board knows about
 * 
 * @author David Lundin
 *
 */
public class Teller {

	/**
	 * Teller ID from the database
	 */
	public int tellerID;
	
	/**
	 * The name of the teller.
	 */
	public String name;
	
	/**
	 * The address of the teller.
	 */
	public String address;
	
	/**
	 * The server name on the teller server.
	 */
	public String serverName;

	/**
	 * The public key of the teller.
	 */
	public PublicKey publicKey;

	/**
	 * The sequence number of the teller
	 */
	public int sequenceNumber;
	
	/**
	 * The teller that we are connected to.
	 */
	public TellerInterface remoteTeller;
	
	/**
	 * Boolean representing the status of the connection
	 * (the connectionState string is humanly legible)
	 */
	public boolean connectionStatus = false;
	
	/**
	 * A string describing the state of the connection
	 * to this teller over RMI
	 */
	public String connectionState = "No Connection";
	
	/**
	 * Whether or not the bulletin board has tested
	 * the identity of this teller or not
	 */
	public boolean handshakeStatus = false;
	
	/**
	 * A count of the number of connection errors
	 * caused during this run of the software
	 */
	public int connectionErrorCount = 0;
	
	/**
	 * A thread that keeps trying to connect to the remote
	 * teller as long as it is not connected
	 */
	public TellerConnectorThread tellerConnectorThread;
	
	/**
	 * Those listening to the TellerUpdatedEvent
	 */
	private ArrayList tellerUpdatedListeners = new ArrayList();
	
	/**
	 * When the teller connects to the web bulletin board and
	 * wishes to identify itself the wbb stores a nonce in this
	 * variable and the teller must then sign this to complete
	 * the identification.
	 */
	public byte[] identificationNonce;
	
	/**
	 * Constructor
	 */
	public Teller(int tellerID, String name, String address, String serverName, PublicKey publicKey, int sequenceNumber) {
		//Store the details
		this.tellerID = tellerID;
		this.name = name;
		this.address = address;
		this.serverName = serverName;
		this.publicKey = publicKey;
		this.sequenceNumber = sequenceNumber;

		//Start a connector thread
		this.tellerConnectorThread = new TellerConnectorThread(this);
		this.tellerConnectorThread.start();
	}
	
	/**
	 * Reveals two layers by invoking the .reveal() method on the remote teller
	 * 
	 * @param onion Onion to be decrypted
	 * @return An ArrayList containing the constituents of the teller's two layers
	 * @throws TellerDownException
	 */
	public ArrayList reveal(Onion onion) throws TellerDownException {
		//An empty result
		ArrayList result = null;
		
		//Check if properly connected
		if(!this.connectionStatus) {
			this.incrementConnectionErrorCount();
			throw new TellerDownException("Currently not connected to teller " + this.tellerID, this.tellerID);
		}
		
		//Try to get result from teller
		try {
			
			result = remoteTeller.reveal(onion);
			
		} catch (RemoteException e) {
			
			//Unable to connect so start thread to retry
			e.printStackTrace();
			this.connectionStatus = false;
			this.connectionState = "RemoteException on .reveal()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was a RemoteException when trying to invoke .reveal() on teller " + this.tellerID, this.tellerID);

		} catch (InvalidKeyException e) {
			
			//Unable to connect so start thread to retry
			this.connectionStatus = false;
			this.connectionState = "InvalidKeyException on .reveal()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was an InvalidKeyException when trying to invoke .reveal() on teller " + this.tellerID, this.tellerID);

		}
		
		//Return whatever we now have
		return result;
	}

	/**
	 * Connects a teller over RMI
	 *
	 */
	public boolean connect() {
		
		try {

			//Connect using RMI
			this.remoteTeller = (TellerInterface)Naming.lookup("rmi://" + this.address + "/" + this.serverName);
			
			//Set connection status to connected
			this.connectionStatus = true;
			this.connectionState = "Connected";
			this.fireTellerUpdatedEvent();
			return true;
			
		} catch (RemoteException ex) {
			
			this.connectionStatus = false;
			this.connectionState = "Failed: RemoteException";
			this.fireTellerUpdatedEvent();
			return false;
			
		} catch (NotBoundException ex) {
			
			this.connectionStatus = false;
			this.connectionState = "Failed: NotBoundException";
			this.fireTellerUpdatedEvent();
			return false;
			
		} catch (MalformedURLException ex) {
			
			this.connectionStatus = false;
			this.connectionState = "Failed: MalformedURLException";
			this.fireTellerUpdatedEvent();
			return false;
			
		}
		
	}
	
	/**
	 * Increments the count of the number of connection errors during
	 * this execution of the program.
	 *
	 */
	public void incrementConnectionErrorCount() {
		//Increment the counter
		this.connectionErrorCount++;
		
		//Tell anyone who is listening
		this.fireTellerUpdatedEvent();
	}
	
	/**
	 * Adds a TellerUpdatedEvent listener
	 * 
	 * @param listener
	 */
	public void addTellerUpdatedListener(TellerUpdatedListener listener) {
		this.tellerUpdatedListeners.add(listener);
	}

	/**
	 * Removes a listener for the TellerUpdatedEvent
	 * 
	 * @param listener
	 */
	public void removeTellerUpdatedListener(TellerUpdatedListener listener) {
		this.tellerUpdatedListeners.remove(listener);
	}
	
	/**
	 * Fires the TellerUpdatedEvent
	 *
	 */
	private void fireTellerUpdatedEvent() {
		//All the listeners
		Iterator listeners = this.tellerUpdatedListeners.iterator();
		
		//Fire on each listener
		while(listeners.hasNext()) {
			((TellerUpdatedListener)listeners.next()).receiveTellerUpdatedEvent(new TellerUpdatedEvent(this));
		}
	}
	
	/**
	 * Submits batch to tellers
	 * 
	 * @param batch
	 */
	public ArrayList processVote(int election, int race, int batchID, TellerBatch batch) throws TellerDownException {
		//An empty result
		ArrayList result = null;
		
		//Check if properly connected
		if(!this.connectionStatus) {
			this.incrementConnectionErrorCount();
			throw new TellerDownException("Currently not connected to teller " + this.name + " (" + this.tellerID + ")", this.tellerID);
		}
		
		//Try to get result from teller
		try {
			
			result = remoteTeller.processVote(election, race, batchID, batch);
			
		} catch (RemoteException e) {
			
			//Unable to connect so start thread to retry
			e.printStackTrace();
			this.connectionStatus = false;
			this.connectionState = "RemoteException on .processVote()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was a RemoteException when trying to invoke .processVote() on teller " + this.tellerID, this.tellerID);

		} catch (InvalidKeyException e) {
			
			//Unable to connect so start thread to retry
			this.connectionStatus = false;
			this.connectionState = "InvalidKeyException on .processVote()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was an InvalidKeyException when trying to invoke .processVote() on teller " + this.tellerID, this.tellerID);

		}
		
		//Return whatever we now have
		return result;
	}
	
	/**
	 * Get a commitment to a value from the teller
	 * 
	 * @param election The election for which to get a commitment
	 * @param race The race for which to get a commitment
	 * @return The commitment
	 */
	public byte[] getCommitment(int election, int race, byte[] random) throws TellerDownException {

		//Check if properly connected
		if(!this.connectionStatus) {
			this.incrementConnectionErrorCount();
			throw new TellerDownException("Currently not connected to teller " + this.name + " (" + this.tellerID + ")", this.tellerID);
		}
		
		//Try to get result from teller
		try {
			
			return remoteTeller.getCommitment(election, race, random);
			
		} catch (RemoteException e) {
			
			//Unable to connect so start thread to retry
			e.printStackTrace();
			this.connectionStatus = false;
			this.connectionState = "RemoteException on .getCommitment()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was a RemoteException when trying to invoke .getCommitment() on teller " + this.tellerID, this.tellerID);

		}
		
	}
	
	/**
	 * Get the value previously committed to
	 * 
	 * @param election The election for which to get the previously committed value
	 * @param race The race for which to get the previously committed value
	 * @return The committed value as NonceBitmapCouple object
	 */
	public NonceBitmapCouple getValue(int election, int race) throws TellerDownException {

		//Check if properly connected
		if(!this.connectionStatus) {
			this.incrementConnectionErrorCount();
			throw new TellerDownException("Currently not connected to teller " + this.name + " (" + this.tellerID + ")", this.tellerID);
		}
		
		//Try to get result from teller
		try {
			
			return remoteTeller.getValue(election, race);
			
		} catch (RemoteException e) {
			
			//Unable to connect so start thread to retry
			e.printStackTrace();
			this.connectionStatus = false;
			this.connectionState = "RemoteException on .getValue()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was a RemoteException when trying to invoke .getValue() on teller " + this.tellerID, this.tellerID);

		}
		
	}

	/**
	 * Challenges the teller
	 * 
	 * @param election The election to audit
	 * @param race The race to audit
	 * @param batchID The batch to audit
	 * @param mask The mask used to audit
	 * @return A list of the revealed information
	 * @throws TellerDownException
	 */
	public ArrayList audit(int election, int race, int batchID, BigInteger mask) throws TellerDownException {

		//Check if properly connected
		if(!this.connectionStatus) {
			this.incrementConnectionErrorCount();
			throw new TellerDownException("Currently not connected to teller " + this.name + " (" + this.tellerID + ")", this.tellerID);
		}
		
		//Try to get result from teller
		try {
			
			return remoteTeller.audit(election, race, batchID, mask);
			
		} catch (RemoteException e) {
			
			//Unable to connect so start thread to retry
			e.printStackTrace();
			this.connectionStatus = false;
			this.connectionState = "RemoteException on .audit()";
			this.incrementConnectionErrorCount();
			this.fireTellerUpdatedEvent();
			throw new TellerDownException("There was a RemoteException when trying to invoke .audit() on teller " + this.tellerID, this.tellerID);

		}
		
	}
	
	public void doHandshake() throws TellerDownException {

		//Check if properly connected
		if(!this.connectionStatus) {
			this.incrementConnectionErrorCount();
			throw new TellerDownException("Currently not connected to teller " + this.name + " (" + this.tellerID + ")", this.tellerID);
		}
		
		//Try to get result from teller
		try {
			
			//Create a nonce
			byte[] nonce = new byte[1000];
			Random random = new Random();
			random.nextBytes(nonce);
				
			//Get the signed nonce
			byte[] signedNonce = remoteTeller.handShake(nonce);

			//Set up a signature
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initVerify(this.publicKey);
				
			//Add the nonce to the signature
			signature.update(nonce);
				
			//Return the signature
			if(signature.verify(signedNonce)) {
				this.handshakeStatus = true;
			} else {
				this.handshakeStatus = false;
			}
			
		} catch (NoSuchAlgorithmException e) {
			
			this.handshakeStatus = false;
			e.printStackTrace();
			
		} catch (InvalidKeyException e) {
			
			this.handshakeStatus = false;
			e.printStackTrace();

		} catch (SignatureException e) {
			
			this.handshakeStatus = false;
			e.printStackTrace();

		} catch (RemoteException e) {
			
			//Unable to connect so start thread to retry
			e.printStackTrace();
			this.connectionStatus = false;
			this.connectionState = "RemoteException on .doHandshake()";
			this.incrementConnectionErrorCount();
			throw new TellerDownException("There was a RemoteException when trying to invoke .doHandshake() on teller " + this.tellerID, this.tellerID);

		} finally {
			
			//Update the table
			this.fireTellerUpdatedEvent();

		}

	}

}
