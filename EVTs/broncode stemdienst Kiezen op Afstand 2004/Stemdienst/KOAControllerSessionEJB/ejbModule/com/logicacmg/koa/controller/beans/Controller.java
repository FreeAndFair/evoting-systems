/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.beans.Controller.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		14-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.controller.beans;
import java.security.PublicKey;
import java.util.Vector;

import com.logicacmg.koa.controller.subscription.ClientSubscription;
import com.logicacmg.koa.dataobjects.CallResult;
import com.logicacmg.koa.exception.KOAException;
/**
 * Remote interface for Enterprise Bean: Controller
 * The controller is responsible for notifying all the other 
 * components in the KOA system when state is changed.The controller
 * also collects all the counters from the other components
 * for concistency checks.
 * 
 * @author KuijerM
 */
public interface Controller extends javax.ejb.EJBObject
{
	/**
	 * Get the public key for the KAO system
	 * 
	 * @return PublicKey the public key for the KOA system
	 * 
	 */
	public PublicKey getPublicKey() throws java.rmi.RemoteException;
	/**
	 * Initialize the KOA system. For the initialization
	 * the public key is given. This is the public key 
	 * that will be used through the hole life cycle of 
	 * the elections.
	 * 
	 * The chairman starts this action.
	 * 
	 * @param pkPublicKey The public key
	 * 
	 * @return CallResult The result of the initialization
	 * 
	 */
	public CallResult initialize(PublicKey pkPublicKey)
		throws java.rmi.RemoteException, KOAException;
	/**
	 * Re-Initialize the KOA system. For this change in state
	 * the public key is given. This should be the same public key
	 * as the public key given when the system was initialized.
	 *
	 * The chairman starts this action.
	 * 
	 * @param pkPublicKey The public key
	 * 
	 * @return CallResult The result of the re-initialization
	 * 
	 */
	public CallResult reInitialize(PublicKey pkPublicKey)
		throws java.rmi.RemoteException, KOAException;
	/**
	 * Open the KOA system. The system is open for the 
	 * elections now.
	 *
	 * The chairman starts this action.
	 * 
	 * @return CallResult The result of the opening
	 * 
	 */
	public CallResult open() throws java.rmi.RemoteException, KOAException;
	/**
	 * Suspend the elections. The KOA system is not open for voting,
	 * because the chairman has suspended the system. The system should 
	 * be re-initialized and opened to open the elections again.
	 *
	 * The chairman starts this action.
	 * 
	 * @return CallResult The result of the suspend action
	 * 
	 */
	public CallResult suspend() throws java.rmi.RemoteException, KOAException;
	/**
	 * Close the elections. At the end of the elections the system is 
	 * closed. It is not possible to vote anymore.
	 *
	 * The chairman starts this action.
	 * 
	 * @return CallResult The result of the closing
	 * 
	 */
	public CallResult close() throws java.rmi.RemoteException, KOAException;
	/**
	 * Prepare the system to count the votes. This action opens the ESB to
	 * prepare the system for counting the votes. The chairman sends his 
	 * private key so the ESB can be opened.
	 *
	 * The chairman starts this action.
	 * 
	 * @param baPrivateKey byte representation of the private key of the chairman
	 * @param sPassword The password used to encrypt the private key
	 *
	 * @return CallResult The result of preparing the vote count
	 * 
	 */
	public CallResult prepareVoteCount(byte[] baPrivateKey, String sPassword)
		throws java.rmi.RemoteException, KOAException;
	/**
	 * Count the votes in the ESB. The count results are stored in the database.
	 * 
	 * The chairman starts this action.
	 * 
	 * @return CallResult the result status of the vote count
	 * 
	 */
	public CallResult countVote()
		throws java.rmi.RemoteException, KOAException;
	/**
	 * Every component that wants to subscribe must request this first.
	 * This is done through this method. 
	 * 
	 * @param sComponentType The componenttype that is requesting the subscription
	 * 
	 * @return String The JNDI name to use to subscribe
	 * 
	 * @throws KOAException when the unique jndi name can not be garanteed.
	 * 
	 */
	public String requestSubscription(String sComponentType)
		throws java.rmi.RemoteException, KOAException;
	/**
	 * After subscribing, the component that has subscribed will 
	 * return a ClientSubscription with all the information about the
	 * subscription. The controller can use this client interface
	 * to notify the client and collect the counters.
	 * 
	 * @param xClient The client subscription 
	 * 
	 * @return String the current state
	 * 
	 * @throws KOAException if something goes wrong during the completion of the subscription
	 *  
	 */
	public String subscriptionComplete(ClientSubscription xClient)
		throws java.rmi.RemoteException, KOAException;
	/**
	 * Returns the current state of the KOA system.
	 * 
	 * @return String containing the current state
	 * 
	 */
	public String getCurrentState()
		throws java.rmi.RemoteException, KOAException;
	/**
	 * get all available states that can be changed to
	 * based on the current state
	 * 
	 * @param sCurrentState the current state
	 * 
	 * @result Vector with a set of states (Strings) that can be changed to
	 * 
	 */
	public Vector getAvailableStates(String sCurrentState)
		throws java.rmi.RemoteException;
	/**
	 * View the most recent counter values from the database
	 * 
	 * @return Vector returns a vector with per component type the counters for that component type
	 * 
	 */
	public Vector getCurrentCounters() throws java.rmi.RemoteException;
	/**
	 * Public remote method to initiate the
	 * collection of all the counters. The counter 
	 * values are saved in the database.
	 * 
	 * @param sInitiationAction action indication the initiation of the collection of the counters.
	 * 
	 */
	public void collectCounters(String sInitiationAction, int timing)
		throws java.rmi.RemoteException;
	/**
	 * Prepare the KOA system. internal tables are reset
	 * 
	 * The chairman starts this action.
	 * 
	 * @param pkPublicKey The public key
	 * 
	 * @return CallResult The result
	 * 
	 */
	public CallResult prepare() throws java.rmi.RemoteException, KOAException;
	/**
	 * unsubscribe a component from the controller
	 * The component will be deleted from the database
	 * and will be removed from the list with clients.
	 * 
	 * @param sComponentID the unique ComponentID from the component that will be unsubscribed.
	 * 
	 * @throws KOAException Exception when something goes wrong unsubscribing.
	 * 
	 */
	public void unsubscribe(String sComponentID)
		throws KOAException, java.rmi.RemoteException;
	/**
	 * Block the KOA system. The system is not open for voting,
	 * because the KOA system has encountered inconsistenties. 
	 * The system should be suspended by the chairman, 
	 * re-initialized and opened to open the elections again.
	 *
	 * The KOA system starts this action.
	 * 
	 */
	public void block() throws KOAException, java.rmi.RemoteException;
	/**
	 * REturns the first next unique number from the database
	 * 
	 * @return int unique number
	 * 
	 * @throws KOAException exception when something goes wrong
	 * 
	 */
	public int getNextSequenceNumber()
		throws KOAException, java.rmi.RemoteException;
	/**
	 * Returns the value of the result of checking if two pincodes
	 * exist and are not equal 
	 * 
	 * @return CallResult The result
	 * 
	 * @throws KOAException exception when somethig goes wrong
	 */
	public CallResult checkPinCode(String sPincode1, String sPincode2)
		throws KOAException, java.rmi.RemoteException;
}
