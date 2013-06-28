/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.beans.ControllerBean.java
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
import java.rmi.RemoteException;
import java.security.MessageDigest;
import java.security.PublicKey;
import java.sql.Timestamp;
import java.util.Enumeration;
import java.util.Vector;

import com.logica.eplatform.error.ErrorMessageFactory;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.SubscriptionManager;
import com.logicacmg.koa.controller.beans.Koa_state;
import com.logicacmg.koa.controller.beans.Koa_stateHome;
import com.logicacmg.koa.controller.subscription.ClientSubscription;
import com.logicacmg.koa.dataobjects.CallResult;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.db.ControllerDB;
import com.logicacmg.koa.esb.beans.ESBSessionEJB;
import com.logicacmg.koa.esb.beans.ESBSessionEJBHome;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.security.KOAEncryptionUtil;
import com.logicacmg.koa.security.KOAPublicKey;
import com.logicacmg.koa.session.beans.UtilitySessionEJB;
import com.logicacmg.koa.session.beans.UtilitySessionEJBHome;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: Controller
 * The controller is responsible for notifying all the other 
 * components in the KOA system when state is changed.The controller
 * also collects all the counters from the other components
 * for concistency checks.
 * 
 * @author KuijerM
 */
public class ControllerBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	/**
	 * getSessionContext
	 */
	public javax.ejb.SessionContext getSessionContext()
	{
		return mySessionCtx;
	}
	/**
	 * setSessionContext
	 */
	public void setSessionContext(javax.ejb.SessionContext ctx)
	{
		mySessionCtx = ctx;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
	}
	/**
	 * ejbCreate
	 */
	public void ejbCreate() throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove()
	{
	}
	/**
	 * Public remote method to initiate the
	 * collection of all the counters. The counter 
	 * values are saved in the database.
	 * 
	 * @param sInitiationAction action indication the initiation of the collection of the counters.
	 */
	public void collectCounters(String sInitiationAction, int timing)
	{
		SubscriptionManager.resetCommunicationFailed();
		/* now collect all the counters */
		this.privateCollectCounters(sInitiationAction, timing);
	}
	/**
	 * private method to initiate the
	 * collection of all the counters. The counter 
	 * values are saved in the database.
	 * 
	 * @param sInitiationAction action indication the initiation of the collection of the counters.
	 * @param timing The moment when counters are collected
	 * @param bResetCommFailure boolean indicating to reset comm failure (true) or not (false)
	 * 
	 */
	private void privateCollectCounters(String sInitiationAction, int timing)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.collectCounters] Start collecting counters");
		/* init variables */
		Vector vSubscribers = new Vector();
		int iGroupID = -1;
		ControllerDB xControllerDB = new ControllerDB();
		/* Determine reasoncode from sInitiationAction */
		int reason;
		if (sInitiationAction.equals(CounterKeys.INIT_SCHEDULER)
			|| (timing == CounterKeys.COUNTBEFORE))
		{
			reason = CounterKeys.PERIODIC;
		}
		else
		{
			reason = CounterKeys.STATECHANGE;
		}
		try
		{
			/* get all the subscribers */
			vSubscribers = SubscriptionManager.getSubscribers();
		}
		catch (KOAException koae)
		{
			/* if something goes wrong log an error and return the CallResult */
			KOALogHelper.logError(
				"ControllerBean.collectCounters",
				"Could not obtain list of subscribers",
				koae);
			return;
		}
		/* get the enumeration of all the subscribers */
		Enumeration enum = vSubscribers.elements();
		ClientSubscription xSubscription = null;
		CounterData xCounterData = null;
		Timestamp tsTimestamp = new Timestamp(System.currentTimeMillis());
		while (enum.hasMoreElements())
		{
			xSubscription = (ClientSubscription) enum.nextElement();
			try
			{
				/* collect the counter */
				xCounterData = xSubscription.collectCounters(reason);
				if (iGroupID == -1)
				{
					/* if we dont have a group id, get it */
					iGroupID = xControllerDB.getCounterGroupID();
				}
				/* insert the counter data in the database */
				xControllerDB.insertCounterData(
					iGroupID,
					tsTimestamp,
					sInitiationAction,
					xCounterData);
			}
			catch (KOAException koae)
			{
				SubscriptionManager.setCommunicationFailed(
					xSubscription.getComponentID());
				KOALogHelper.logError(
					"ControllerBean.collectCounters",
					"Problem getting counters for component with JNDI "
						+ xSubscription.getJNDIName(),
					koae);
			}
		}
	}
	/**
	 * View the most recent counter values from the database
	 * 
	 * @return Vector returns a vector with per component type the counters for that component type
	 */
	public Vector getCurrentCounters()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.getCurrentCounters] get the current counter values");
		ControllerDB xControllerDB = new ControllerDB();
		Vector vCounters = null;
		/* Retrieve most recent counters from db  */
		try
		{
			vCounters = xControllerDB.getCurrentCounters();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerBean.getCurrentCounters",
				"Could not obtain current counters. KOAException has occured",
				koae);
		}
		/* return the vector */
		return vCounters;
	}
	/**
	 * Get the public key for the KAO system
	 * Returns null if no public key can be obtained.
	 * 
	 * @return PublicKey the public key for the KOA system
	 * 
	 */
	public PublicKey getPublicKey()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.getPublicKey] get the public key");
		PublicKey pkPublicKey = null;
		try
		{
			/* get the public key from the database */
			ControllerDB xControllerDB = new ControllerDB();
			pkPublicKey = xControllerDB.loadPublicKey();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerBean.getPublicKey",
				"Error loading public key",
				koae);
		}
		return pkPublicKey;
	}
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
	public CallResult prepare() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.prepare] prepare the KOA system");
		CallResult xCallResult = null;
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.PREPARE))
		{
			/* change the state to initialized */
			xCallResult = changeState(SystemState.PREPARE);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.prepare] KOA system is prepared...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.prepare] the state change is not valid. System is not initialized...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		/* return the result */
		return xCallResult;
	}
	/**
	 * Initialize the KOA system. For the initialization
	 * the public key is given. This is the public key 
	 * that will be used through the whole life cycle of 
	 * the elections.
	 * 
	 * The chairman starts this action.
	 * 
	 * @param pkPublicKey The public key
	 * 
	 * @return CallResult The result of the initialization
	 * 
	 */
	public CallResult initialize(PublicKey pkPublicKey) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.initialize] initialize the KOA system");
		CallResult xCallResult = null;
		/* Check if the publickey is empty */
		if (pkPublicKey == null)
		{
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.PUBLIC_KEY_EMPTY);
			xCallResult.setMessage(CallResult.EMPTY_PUBLIC_KEY);
			xCallResult.setCurrentState(this.getCurrentState());
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.initialize] public key is empty");
			return xCallResult;
		}
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.INITIALIZED))
		{
			/* save the public key */
			this.savePublicKey(pkPublicKey);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.initialize] public key saved...");
			/* change the state to initialized */
			xCallResult = changeState(SystemState.INITIALIZED);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.initialize] KOA system is initialized...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.initialize] the state change is not valid. System is not initialized...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		/* return the result */
		return xCallResult;
	}
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
	public CallResult reInitialize(PublicKey pkPublicKey) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.reInitialize] re-initialize the KOA system");
		CallResult xCallResult = null;
		/* Check if the publickey is empty */
		if (pkPublicKey == null)
		{
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.PUBLIC_KEY_EMPTY);
			xCallResult.setMessage(CallResult.EMPTY_PUBLIC_KEY);
			xCallResult.setCurrentState(this.getCurrentState());
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.initialize] public key is empty");
			return xCallResult;
		}
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.RE_INITIALIZED))
		{
			PublicKey pkOldPublicKey = KOAPublicKey.getPublicKey();
			if (KOAEncryptionUtil
				.comparePublicKey(pkPublicKey, pkOldPublicKey))
			{
				/* change the state to re-initialized */
				xCallResult = changeState(SystemState.RE_INITIALIZED);
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.reInitialize] KOA system is re-initialized...");
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.reInitialize] Public key provided for reinit is not the same as the public key provided for init...");
				xCallResult = new CallResult();
				xCallResult.setResult(CallResult.PUBLIC_KEYS_NOT_SAME);
				xCallResult.setMessage(
					"De public key meegegeven voor herinitialisatie is niet gelijk aan public key meegegeven voor initialisatie.");
				xCallResult.setCurrentState(this.getCurrentState());
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[ControllerBean.reInitialize] the state change is not valid. System is not re-initialized...");
			}
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.reInitialize] the state change is not valid. System is not re-initialized...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		/* return the result */
		return xCallResult;
	}
	/**
	 * Open the KOA system. The system is open for the 
	 * elections now.
	 *
	 * The chairman starts this action.
	 * 
	 * @return CallResult The result of the opening
	 * 
	 */
	public CallResult open() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.open] open the KOA system");
		CallResult xCallResult = null;
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.OPEN))
		{
			/* change the state to open */
			xCallResult = changeState(SystemState.OPEN);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.open] KOA System is open...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.open] the state change is not valid. System is not open...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		/* return the result */
		return xCallResult;
	}
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
	public CallResult suspend() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.suspend] KOA System will be suspended...");
		CallResult xCallResult = null;
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.SUSPENDED))
		{
			/* change the state to suspended */
			xCallResult = changeState(SystemState.SUSPENDED);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.suspend] KOA system is suspended...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.suspend] the state change is not valid. System is not suspended...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		return xCallResult;
	}
	/**
	 * OR 22.3.602 Gebruik pincode voor statuswijziging
	 * Checks if the pincodes exist and are not equal.
	 * 
	 * @return The result of the pincode check action
	 * 
	 * @throws KOAException exception when something goes wrong
	 */
	public CallResult checkPinCode(String sPinCode1, String sPinCode2)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.checkPinCode] pincodes will be checked...");
		String sPin1 = null;
		String sPin2 = null;
		CallResult xCallResult = new CallResult();
		ControllerDB xControllerDB = new ControllerDB();
		/* Set current state if no valid state change */
		xCallResult.setCurrentState(this.getCurrentState());
		// Check if the pincode fields are left empty
		if (sPinCode1 == null
			|| sPinCode2 == null
			|| sPinCode1.equals("")
			|| sPinCode2.equals(""))
		{
			xCallResult.setResult(CallResult.PINCODE_EMPTY);
			xCallResult.setMessage(CallResult.EMPTY_FIELD);
			return xCallResult;
		}
		// The pincode fields are not empty.Check now if the two pincodes are unique
		if (sPinCode1.equals(sPinCode2))
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.checkPinCode] Both pincodes are the same...");
			//xCallResult = new CallResult ();
			xCallResult.setResult(CallResult.PINCODE_NOT_UNIQUE);
			xCallResult.setMessage(CallResult.NOT_UNIQUE);
			return xCallResult;
		}
		// The pincodes are unique. Now check the syntax.
		// check if pincode1 is numeric
		for (int i = 0; i < sPinCode1.length(); i++)
		{
			char cCharFromPincode1 = sPinCode1.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromPincode1))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[ControllerBean.checkPincode] pincode1 is niet numeriek");
				xCallResult.setResult(CallResult.PINCODE_NOT_NUMERIC);
				xCallResult.setMessage(CallResult.NOT_NUMERIC);
				return xCallResult;
			}
		}
		// check if pincode1 is not longer then 5 digits
		if (sPinCode1.length() != 5)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ControllerBean.checkPincode] pincode1 bestaat niet uit 5 karakters");
			xCallResult.setResult(CallResult.PINCODE_NOT_CORRECT_LENGTH);
			xCallResult.setMessage(CallResult.NOT_CORRECT_LENGTH);
			return xCallResult;
		}
		//check if pincode2 is numeric
		for (int i = 0; i < sPinCode2.length(); i++)
		{
			char cCharFromPincode2 = sPinCode2.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromPincode2))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[ControllerBean.checkPincode] pincode2 is niet numeriek");
				xCallResult.setResult(CallResult.PINCODE_NOT_NUMERIC);
				xCallResult.setMessage(CallResult.NOT_NUMERIC);
				return xCallResult;
			}
		}
		// check if pincode2 is not longer then 5 digits
		if (sPinCode2.length() != 5)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ControllerBean.checkPincode] pincode2 bestaat niet uit 5 karakters");
			xCallResult.setResult(CallResult.PINCODE_NOT_CORRECT_LENGTH);
			xCallResult.setMessage(CallResult.NOT_CORRECT_LENGTH);
			return xCallResult;
		}
		// Both pincodes are syntactically correct. Now hash the pincodes to compare
		// with the stored pincodes in the database.
		try
		{
			sPin1 = hashPinCode(sPinCode1);
			sPin2 = hashPinCode(sPinCode2);
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[prepareVoteCount.init] error occured while hashing the pincode");
			throw new KOAException(ErrorConstants.SECURITY_HASHING_PINCODE, e);
		}
		// Both pincodes are hashed. Now check if they exist in the database
		try
		{
			if (xControllerDB.checkPinCode(sPin1, sPin2) == true)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.checkPinCodes] ++++++++++++++++++");
				// The pincodes exist, set result to OK
				xCallResult.setResult(CallResult.RESULT_OK);
				// Everything went ok!
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.checkPinCodes] Both pincodes are validated...");
			}
			else
			{
				// One or all the pincode(s) do not exists, set result to NOT_EXIST
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.checkPinCodes] One or two of the pincodes do not exist in the database...");
				xCallResult.setResult(CallResult.PINCODE_NOT_EXIST);
				xCallResult.setMessage(CallResult.NOT_EXIST);
			}
			return xCallResult;
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerBean.checkPinCodes",
				"Error checking pincode",
				koae);
			xCallResult.setResult(CallResult.ERROR_DURING_CALL);
			xCallResult.setMessage(CallResult.PINCODE_ERROR);
			return xCallResult;
		}
	}
	/**
	 * Block the KOA system. The system is not open for voting,
	 * because the KOA system has encountered inconsistenties. 
	 * The system should be suspended by the chairman, 
	 * re-initialized and opened to open the elections again.
	 *
	 * The KOA system starts this action.
	 * 
	 */
	public void block() throws KOAException
	{
		/* change the state to blocked this can always be done */
		String sCurrentState = this.getCurrentState();
		SubscriptionManager.resetCommunicationFailed();
		if (sCurrentState.equals(SystemState.PREPARE)
			|| sCurrentState.equals(SystemState.INITIALIZED)
			|| sCurrentState.equals(SystemState.CLOSED)
			|| sCurrentState.equals(SystemState.READY_TO_COUNT)
			|| sCurrentState.equals(SystemState.VOTES_COUNTED))
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ControllerBean.block] Block is not needed in the current state...");
			/* dont do anything */
			return;
		}
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"[ControllerBean.block] KOA System has found inconsistencies, KOA is blocking the system...");
		KOALogHelper.logErrorCode(
			"ControllerBean.block",
			ErrorConstants.ERR_RESULT_BLOCK_SYSTEM,
			null,
			null);
		if (sCurrentState.equals(SystemState.BLOCKED))
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.block] Cannot block system, system already blocked...");
			return;
		}
		/* log the audit record */
		String[] startParams =
			{
				SystemState.getDutchTranslationForState(sCurrentState),
				SystemState.getDutchTranslationForState(SystemState.BLOCKED)};
		KOALogHelper.log(
			KOALogHelper.WARNING,
			this.getMessage(
				ErrorConstants.CHANGE_STATE_AUDIT_START_CHANGE,
				startParams));
		/* save the state */
		this.saveState(SystemState.BLOCKED);
		/* try to log a record to the audit log */
		try
		{
			String sMessage =
				ErrorMessageFactory.getErrorMessageFactory().getErrorMessage(
					ErrorConstants.CHANGE_STATE_BLOCKING,
					null);
			this.logAuditLog(
				KOALogHelper.ERROR,
				AuditEventListener.STATE_CHANGE,
				"Systeem",
				sMessage);
		}
		catch (Exception e)
		{
			//you cant say i didnt try
		}
		/* notify all components */
		this.notifyAll(sCurrentState, SystemState.BLOCKED, false);
		this.privateCollectCounters(
			"CHANGE_STATE_TO_" + SystemState.BLOCKED,
			CounterKeys.COUNTAFTER);
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"[ControllerBean.block] KOA System is blocked...");
	}
	/**
	 * Close the elections. At the end of the elections the system is 
	 * closed. It is not possible to vote anymore.
	 *
	 * The chairman starts this action.
	 * 
	 * @return CallResult The result of the closing
	 * 
	 */
	public CallResult close() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.close] KOA System will be closed...");
		CallResult xCallResult = null;
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.CLOSED))
		{
			/* change the state to closed */
			xCallResult = changeState(SystemState.CLOSED);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.close] KOA system is closed...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.close] the state change is not valid. System is not closed...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		return xCallResult;
	}
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
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.prepareVoteCount] KOA System will be prepared for counting votes...");
		CallResult xCallResult = null;
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.READY_TO_COUNT))
		{
			/* change the state to ready to count votes */
			xCallResult = changeState(SystemState.READY_TO_COUNT);
			/* open the ESB with the private key */
			this.openESB(baPrivateKey, sPassword);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.prepareVoteCount] KOA system is prepared to count votes...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.prepareVoteCount] the state change is not valid. System is not prepared to count votes...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		return xCallResult;
	}
	/**
	 * Count the votes in the ESB. The count results are stored in the database.
	 * 
	 * The chairman starts this action.
	 * 
	 * @return CallResult the result status of the vote count
	 * 
	 * @throws KOAException Exception when something goes wrong during counting of the votes
	 * 
	 */
	public CallResult countVote() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.countVote] KOA System will be counting votes...");
		CallResult xCallResult = null;
		/* check if the state change is valid */
		if (this.isValidStateChange(SystemState.VOTES_COUNTED))
		{
			/* count the votes */
			this.countVotesOnESB();
			/* change the state to ready to count votes */
			xCallResult = changeState(SystemState.VOTES_COUNTED);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.countVote] KOA system has counted votes...");
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerBean.countVote] the state change is not valid. System has not counted votes...");
			xCallResult = new CallResult();
			xCallResult.setResult(CallResult.STATE_CHANGE_INVALID);
			xCallResult.setMessage("Deze statuswijziging is niet geldig");
			xCallResult.setCurrentState(this.getCurrentState());
		}
		return xCallResult;
	}
	/**
	 * Every component that wants to subscribe must request this first.
	 * This is done through this method. 
	 * 
	 * The JDNI name will have the structure KOA_COMPONENT_JNDI_[componentType]_[FreeID]
	 * 
	 * @param sComponentType The componenttype that is requesting the subscription
	 * 
	 * @return String The JNDI name to use to subscribe
	 * 
	 * @throws KOAException exception when unique JNDI name can not be garanteed
	 * 
	 */
	public String requestSubscription(String sComponentType)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.requestSubscription] requesting subscription for component type "
				+ sComponentType);
		ControllerDB xControllerDB = new ControllerDB();
		String sUniqueJndiName = "com_logicacmg_koa_controller_client_";
		/* get a unique number from the database */
		int iFreeID = this.getNextSequenceNumber();
		/* create a unique JDNI name for the request */
		sUniqueJndiName += sComponentType;
		sUniqueJndiName += Integer.toString(iFreeID);
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.requestSubscription] returning unique jndi name "
				+ sUniqueJndiName);
		/* return the unique name */
		return sUniqueJndiName;
	}
	/**
	 * REturns the first next unique number from the database
	 * 
	 * @return int unique number
	 * 
	 * @throws KOAException exception when something goes wrong
	 * 
	 */
	public int getNextSequenceNumber() throws KOAException
	{
		ControllerDB xControllerDB = new ControllerDB();
		return xControllerDB.getFreeID();
	}
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
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.subscriptionComplete] subscribing type "
				+ xClient.getComponentType()
				+ " start subscription complete ");
		/* add the client to the subscription manager */
		SubscriptionManager.addSubscriber(xClient);
		/* return the current state as the result */
		return this.getCurrentState();
	}
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
	public void unsubscribe(String sComponentID) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.unsubscribe] unsubscribing component "
				+ sComponentID);
		/* remove the component from subscription manager */
		SubscriptionManager.removeSubscriber(sComponentID);
	}
	/**
	 * Returns the current state of the KOA system.
	 * 
	 * @return String containing the current state
	 * 
	 */
	public String getCurrentState() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.getCurrentState] get the current state");
		String sCurrentState = null;
		try
		{
			/* get the state entity bean */
			Koa_state xState = getStateEntity();
			/* read the current state */
			sCurrentState = xState.getCurrent_state();
		}
		catch (RemoteException re)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ControllerBean.getCurrentState] Remote exception getting current state");
			re.printStackTrace();
			throw new KOAException(ErrorConstants.CONTROLLER_GETSTATE, re);
		}
		return sCurrentState;
	}
	/**
	 * get all available states that can be changed to
	 * based on the current state
	 * 
	 * @param sCurrentState the current state
	 * 
	 * @result Vector with a set of states (Strings) that can be changed to
	 * 
	 */
	public Vector getAvailableStates(String sState)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.getAvailableStates] get all valid available states");
		/* get all the available state changes based on the current state */
		Vector vAvailableStates = SystemState.getValidStateChanges(sState);
		/* return the available states based on the current state */
		return vAvailableStates;
	}
	/**
	 * Changes the current state in memory, in the database 
	 * and for all the components subscribed to the system
	 * 
	 * @param sNewState the new state
	 * 
	 * @return The result status of the propagation of the new state
	 * 
	 */
	private CallResult changeState(String sNewState) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.changeState] start changing state");
		boolean bIsBlocking = sNewState.equals(SystemState.BLOCKED);
		SubscriptionManager.resetCommunicationFailed();
		/* init variables */
		CallResult xCallResult = null;
		/* get the current state */
		String sCurrentState = this.getCurrentState();
		String[] params = { sCurrentState, sNewState };
		KOALogHelper.logErrorCode(
			"ControllerBean.changeState",
			ErrorConstants.INFO_CHANGESTATE_START,
			params,
			null);
		/* log the audit record */
		if (!bIsBlocking)
		{
			String[] startParams =
				{
					SystemState.getDutchTranslationForState(sCurrentState),
					SystemState.getDutchTranslationForState(sNewState)};
			this.logAuditLog(
				KOALogHelper.INFO,
				AuditEventListener.STATE_CHANGE,
				getSessionContext().getCallerPrincipal().getName(),
				this.getMessage(
					ErrorConstants.CHANGE_STATE_AUDIT_START_CHANGE,
					startParams));
		}
		/* check if we have to first change state and 
		after that notify components, or first notify components
		and then change the db system state */
		boolean bChangeSystemChangeFirst =
			SystemState.changeSystemStateFirst(sCurrentState, sNewState);
		boolean bOnlyChangeStateIfNotifySuccesful =
			SystemState.changeStateOnlyForSuccesfulNotify(
				sCurrentState,
				sNewState);
		/* change db first */
		if (bChangeSystemChangeFirst)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.changeState] First changing system state, after that, notifying components");
			/* save the state */
			this.saveState(sNewState);
			/* notify all the subscribers and get current counter values */
			if (sNewState.equals(SystemState.OPEN))
			{
				this.privateCollectCounters(
					"CHANGE_STATE_TO_" + sNewState,
					CounterKeys.COUNTBEFORE);
				xCallResult =
					this.notifyAll(
						sCurrentState,
						sNewState,
						bOnlyChangeStateIfNotifySuccesful);
			}
			else
			{
				xCallResult =
					this.notifyAll(
						sCurrentState,
						sNewState,
						bOnlyChangeStateIfNotifySuccesful);
				this.privateCollectCounters(
					"CHANGE_STATE_TO_" + sNewState,
					CounterKeys.COUNTAFTER);
			}
		}
		/* change db after notifying the components */
		else
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ControllerBean.changeState] First notify components, after that, changing system state");
			/* notify all the subscribers and get current counter values */
			if (sNewState.equals(SystemState.OPEN))
			{
				this.privateCollectCounters(
					"CHANGE_STATE_TO_" + sNewState,
					CounterKeys.COUNTBEFORE);
				xCallResult =
					this.notifyAll(
						sCurrentState,
						sNewState,
						bOnlyChangeStateIfNotifySuccesful);
			}
			else
			{
				xCallResult =
					this.notifyAll(
						sCurrentState,
						sNewState,
						bOnlyChangeStateIfNotifySuccesful);
				this.privateCollectCounters(
					"CHANGE_STATE_TO_" + sNewState,
					CounterKeys.COUNTAFTER);
			}
			/* Only change the state when succeful for certain state changes */
			if (!bOnlyChangeStateIfNotifySuccesful
				|| xCallResult.getResult()
					== CallResult.NOTIFY_STATE_CHANGE_SUCCESFUL
				|| xCallResult.getResult()
					== CallResult.NOTIFY_STATE_CHANGE_WARNING
				/* Also save state if it is a invalid fingerprints */
				|| xCallResult.getResult()
					== CallResult.NOTIFY_STATE_CHANGE_INVALID_FINGERPRINTS)
			{
				/* save the state */
				this.saveState(sNewState);
			}
			else
			{
				KOALogHelper.logError(
					"ControllerBean.changeState",
					"Could not save the state because not all components are notified succesfully of new state",
					null);
			}
		}
		/* set the current state in the response object */
		if (xCallResult != null)
		{
			xCallResult.setCurrentState(this.getCurrentState());
			/* log the audit record */
			if (xCallResult.getResult()
				== CallResult.NOTIFY_STATE_CHANGE_SUCCESFUL)
			{
				String[] saSuccefulParams =
					{
						SystemState.getDutchTranslationForState(sCurrentState),
						SystemState.getDutchTranslationForState(sNewState)};
				if (!bIsBlocking)
				{
					this.logAuditLog(
						KOALogHelper.INFO,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_AUDIT_CHANGE_STATE_SUCCEFUL,
							saSuccefulParams));
				}
				xCallResult.setMessage(
					this.getMessage(
						ErrorConstants.CHANGE_STATE_RESULT_MESSAGE_SUCCESFUL,
						saSuccefulParams));
			}
			else if (
				xCallResult.getResult()
					== CallResult.NOTIFY_STATE_CHANGE_INVALID_FINGERPRINTS)
			{
				String sMessage = "";
				if (xCallResult.getMessage() != null)
				{
					sMessage = xCallResult.getMessage();
				}
				String[] saPartlyParams =
					{
						SystemState.getDutchTranslationForState(sCurrentState),
						SystemState.getDutchTranslationForState(sNewState)};
				if (!bIsBlocking)
				{
					this.logAuditLog(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_AUDIT_INVALID_FINGERPRINTS,
							saPartlyParams));
				}
				xCallResult.setMessage(
					this.getMessage(
						ErrorConstants.CHANGE_STATE_AUDIT_INVALID_FINGERPRINTS,
						saPartlyParams)
						+ " "
						+ sMessage);
			}
			else if (
				xCallResult.getResult()
					== CallResult.NOTIFY_STATE_CHANGE_WARNING)
			{
				String sMessage = "";
				if (xCallResult.getMessage() != null)
				{
					sMessage = xCallResult.getMessage();
				}
				/* Use a list of unsuccesfull components for the return message */
				String sUnsuccesfullComponents = "";
				if (xCallResult.getUnsuccesfullComponents().size() > 0)
				{
					for (int i = 0;
						i < xCallResult.getUnsuccesfullComponents().size();
						i++)
					{
						/* seperate the components with a comma */
						if (i > 0)
						{
							sUnsuccesfullComponents += ", ";
						}
						sUnsuccesfullComponents
							+= (String) xCallResult
								.getUnsuccesfullComponents()
								.get(
								i);
					}
				}
				String[] saPartlyParams =
					{
						SystemState.getDutchTranslationForState(sCurrentState),
						SystemState.getDutchTranslationForState(sNewState),
						sUnsuccesfullComponents };
				if (!bIsBlocking)
				{
					this.logAuditLog(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_AUDIT_CHANGE_STATE_PARTLY,
							saPartlyParams));
				}
				xCallResult.setMessage(
					this.getMessage(
						ErrorConstants.CHANGE_STATE_RESULT_MESSAGE_PARTLY,
						saPartlyParams)
						+ " "
						+ sMessage);
			}
			else
			{
				String sMessage = "";
				if (xCallResult.getMessage() != null)
				{
					sMessage = xCallResult.getMessage();
				}
				/* Use a list of unsuccesfull components for the return message */
				String sUnsuccesfullComponents = "";
				if (xCallResult.getUnsuccesfullComponents().size() > 0)
				{
					for (int i = 0;
						i < xCallResult.getUnsuccesfullComponents().size();
						i++)
					{
						/* seperate the components with a comma */
						if (i > 0)
						{
							sUnsuccesfullComponents += ", ";
						}
						sUnsuccesfullComponents
							+= (String) xCallResult
								.getUnsuccesfullComponents()
								.get(
								i);
					}
				}
				String[] saParamsError =
					{
						SystemState.getDutchTranslationForState(sCurrentState),
						SystemState.getDutchTranslationForState(sNewState),
						sUnsuccesfullComponents };
				if (bOnlyChangeStateIfNotifySuccesful)
				{
					if (!bIsBlocking)
					{
						this.logAuditLog(
							KOALogHelper.ERROR,
							AuditEventListener.STATE_CHANGE,
							getSessionContext().getCallerPrincipal().getName(),
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_AUDIT_CHANGE_STATE_ERROR_NO_CHANGE,
								saParamsError));
					}
					xCallResult.setMessage(
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_RESULT_MESSAGE_ERROR_NO_CHANGE,
							saParamsError)
							+ " "
							+ sMessage);
				}
				else
				{
					if (!bIsBlocking)
					{
						this.logAuditLog(
							KOALogHelper.ERROR,
							AuditEventListener.STATE_CHANGE,
							getSessionContext().getCallerPrincipal().getName(),
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_AUDIT_CHANGE_STATE_ERROR_CHANGE,
								saParamsError));
					}
					xCallResult.setMessage(
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_RESULT_MESSAGE_ERROR_CHANGE,
							saParamsError)
							+ " "
							+ sMessage);
				}
			}
		}
		return xCallResult;
	}
	/**
	 * Save the state to the entity bean
	 * 
	 * @return boolean indicating the success of the change
	 * 
	 * @throws KOAException something went wrong during saving of the new state
	 * 
	 */
	private boolean saveState(String sNewState) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.saveState] changing state in database to new state "
				+ sNewState);
		boolean bResult = false;
		boolean bIsBlocking = sNewState.equals(SystemState.BLOCKED);
		/* find the state bean */
		Koa_state xState = getStateEntity();
		/* check if we have a state */
		if (xState != null)
		{
			/* set the state */
			try
			{
				xState.setCurrent_state(sNewState);
				bResult = true;
				/* log the audit record */
				if (!bIsBlocking)
				{
					String[] saParams =
						{ SystemState.getDutchTranslationForState(sNewState)};
					this.logAuditLog(
						KOALogHelper.INFO,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants.CHANGE_STATE_AUDIT_SAVE_STATE,
							saParams));
				}
			}
			catch (RemoteException re)
			{
				bResult = false;
				/* log the audit record */
				if (!bIsBlocking)
				{
					String[] saError = { re.getMessage()};
					this.logAuditLog(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants.CHANGE_STATE_AUDIT_SAVE_STATE_ERROR,
							saError));
				}
				KOALogHelper.logError(
					"ControllerBean.saveState",
					"Remote exception while setting new state. State not set ",
					re);
				throw new KOAException(ErrorConstants.CONTROLLER_SAVESTATE, re);
			}
		}
		else
		{
			bResult = false;
			/* log the audit record */
			if (!bIsBlocking)
			{
				this.logAuditLog(
					KOALogHelper.ERROR,
					AuditEventListener.STATE_CHANGE,
					getSessionContext().getCallerPrincipal().getName(),
					this.getMessage(
						ErrorConstants
							.CHANGE_STATE_AUDIT_SAVE_STATE_UNKNOWN_ERROR,
						null));
			}
			KOALogHelper.logError(
				"ControllerBean.saveState",
				"Error finding bean, State not updated",
				null);
			throw new KOAException(ErrorConstants.CONTROLLER_SAVESTATE);
		}
		return bResult;
	}
	/**
	 * Checks if the state change is a valid change.
	 * 
	 * @param sNewState The new requested state
	 * 
	 * @return boolean indicating if the state change is valid (true) or not valid (false)
	 * 
	 * @throws KOAException exception when something goes wrong checking the state change
	 * 
	 */
	private boolean isValidStateChange(String sNewState) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.isValidStateChange] start checking if it is a valid state change");
		/* if new state is blocked, the state change is always OK */
		if (sNewState.equals(SystemState.BLOCKED))
		{
			/* this is always an OK state change */
			return true;
		}
		boolean bIsValid = false;
		/* get all the valid state changes for the current state */
		String sCurrentState = this.getCurrentState();
		Vector vValidNew = this.getAvailableStates(sCurrentState);
		Enumeration enum = vValidNew.elements();
		/* loop through all the states */
		String sValidState = null;
		while (enum.hasMoreElements())
		{
			/* get the next valid state */
			sValidState = (String) enum.nextElement();
			/* check if the states are the same */
			if (sNewState.equals(sValidState))
			{
				bIsValid = true;
				break;
			}
		}
		return bIsValid;
	}
	/**
	 * Save the public key to the database and in memory
	 * 
	 * @param pkPublicKey the public key for the encryption
	 * 
	 */
	private void savePublicKey(PublicKey pkPublicKey) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.savePublicKey] start saving public key");
		try
		{
			/* get the public key from the database */
			ControllerDB xControllerDB = new ControllerDB();
			xControllerDB.savePublicKey(pkPublicKey);
		}
		catch (KOAException koae)
		{
			/* Log the error in public key saving for monitor by tivoli */
			String[] params = { "public" };
			KOALogHelper.logErrorCode(
				"ControllerBean.savePublicKey",
				ErrorConstants.ERR_PARSE_PUB_PRIVKEY,
				params,
				koae);
			KOALogHelper.logError(
				"ControllerBean.savePublicKey",
				"Error saving public key",
				koae);
			throw koae;
		}
	}
	/**
	 * method to notify all the subscribed components of a state change.
	 * 
	 * @param sCurrentState The current state the system is in
	 * @param sNewState the new state
	 * @param bOnlyStateChangeWhenSuccesful boolean indicating if the state is changed when the notification is succeful (true) or state is changed when the notification is succeful and not succeful (false);
	 *
	 * @return CallResult the result status
	 *  
	 */
	private CallResult notifyAll(
		String sCurrentState,
		String sNewState,
		boolean bOnlyStateChangeWhenSuccesful)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.notifyAll] start notify all components with new state "
				+ sNewState);
		/* init variables */
		boolean bIsBlockingSystem = sNewState.equals(SystemState.BLOCKED);
		boolean bResult = true;
		boolean bESBandKRresult = true;
		boolean bSetCallResult = true;
		CallResult xCallResult = new CallResult();
		Vector vSubscribers = null;
		boolean bFingerprintError = false;
		try
		{
			/* get all the subscribers */
			vSubscribers = SubscriptionManager.getSubscribers();
		}
		catch (KOAException koae)
		{
			/* if something goes wrong log an error and return the CallResult */
			KOALogHelper.logError(
				"ControllerBean.notifyAll",
				"Could not obtain list of subscribers",
				koae);
			xCallResult.setResult(CallResult.NOTIFY_STATE_CHANGE_ERROR);
			xCallResult.setMessage(
				this.getMessage(
					ErrorConstants.CHANGE_STATE_AUDIT_FIND_SUBSCRIBERS,
					null));
			/* log the audit record */
			if (!bIsBlockingSystem)
			{
				this.logAuditLog(
					KOALogHelper.ERROR,
					AuditEventListener.STATE_CHANGE,
					getSessionContext().getCallerPrincipal().getName(),
					this.getMessage(
						ErrorConstants.CHANGE_STATE_AUDIT_FIND_SUBSCRIBERS,
						null));
			}
			return xCallResult;
		}
		/* init variables */
		ClientSubscription xSubscription = null;
		Enumeration enumeration = null;
		if (sNewState.equals(SystemState.OPEN))
		{
			/* init variables */
			enumeration = vSubscribers.elements();
			boolean bHasKR = false;
			boolean bHasESB = false;
			boolean bHasWSM = false;
			boolean bHasTSM = false;
			/* check if minimal 1 KR, ESB, WSM and TSM is present when where are opening */
			while (enumeration.hasMoreElements())
			{
				xSubscription = (ClientSubscription) enumeration.nextElement();
				if (xSubscription.getComponentType().equals(ComponentType.ESB))
				{
					bHasESB = true;
				}
				else if (
					xSubscription.getComponentType().equals(ComponentType.KR))
				{
					bHasKR = true;
				}
				else if (
					xSubscription.getComponentType().equals(ComponentType.WEB))
				{
					bHasWSM = true;
				}
				else if (
					xSubscription.getComponentType().equals(ComponentType.TEL))
				{
					bHasTSM = true;
				}
			}
			if (bHasESB && bHasKR && bHasTSM && bHasWSM)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.notifyAll] Minimum of 1 KR, ESB, WSM, TSM is subscribed... enough components for opening...");
			}
			else
			{
				KOALogHelper.logError(
					"ControllerBean.notifyAll",
					"Not enougn components in place... WSM present ["
						+ bHasWSM
						+ "] TSM present ["
						+ bHasTSM
						+ "] ESB present ["
						+ bHasESB
						+ "] KR present ["
						+ bHasKR
						+ "]",
					null);
				/* log the audit record */
				if (!bIsBlockingSystem)
				{
					this.logAuditLog(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						"Niet alle componenten zijn aanwezig: WSM aanwezig ["
							+ bHasWSM
							+ "], TSM aanwezig ["
							+ bHasTSM
							+ "], ESB aanwezig ["
							+ bHasESB
							+ "], KR aanwezig ["
							+ bHasKR
							+ "]");
				}
			}
		}
		else if (sNewState.equals(SystemState.INITIALIZED))
		{
			ControllerDB controllerDB = new ControllerDB();
			if (controllerDB.systemContainsCandidates())
			{
				/* log the audit record */
				if (!bIsBlockingSystem)
				{
					this.logAuditLog(
						KOALogHelper.INFO,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants.CHANGE_STATE_CHECK_CANDIDATES_OK,
							null));
				}
			}
			else
			{
				xCallResult.addUnsuccesfullComponentType("Kieslijst");
				KOALogHelper.logError(
					"ControllerBean.notifyAll",
					"No candidates where found in the system databases",
					null);
				/* log the audit record */
				if (!bIsBlockingSystem)
				{
					this.logAuditLog(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants.CHANGE_STATE_CHECK_CANDIDATES_ERROR,
							null));
				}
				if (bOnlyStateChangeWhenSuccesful)
				{
					xCallResult.setResult(CallResult.NOTIFY_STATE_CHANGE_ERROR);
					return xCallResult;
				}
			}
		}
		boolean bHasNotifiedESB = false;
		boolean bHasNotifiedKR = false;
		/* init variables */
		boolean bSuccess = false;
		String sErrorMessage = null;
		for (int i = 0; i < vSubscribers.size(); i++)
		{
			bSuccess = true;
			sErrorMessage = "onbekende technische reden";
			xSubscription = (ClientSubscription) vSubscribers.elementAt(i);
			/* notify the new State */
			if (xSubscription.getComponentType().equals(ComponentType.WEB)
				|| xSubscription.getComponentType().equals(ComponentType.TEL)
				|| xSubscription.getComponentType().equals(ComponentType.STEM)
				|| (xSubscription.getComponentType().equals(ComponentType.ESB)
					&& !bHasNotifiedESB)
				|| (xSubscription.getComponentType().equals(ComponentType.KR)
					&& !bHasNotifiedKR))
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.notifyAll] notify component "
						+ xSubscription.getComponentID());
				try
				{
					/* notify the component */
					bSuccess = xSubscription.notify(sCurrentState, sNewState);
				}
				/* always check the KOAEXception for fingerprint compares */
				catch (KOAException koae)
				{
					/* check for the ESB fingerprint */
					if (koae
						.getErrorCode()
						.equals(ErrorConstants.ESB_FINGERPRINT_ERROR))
					{
						/* log the audit log */
						if (!bIsBlockingSystem)
						{
							this.logAuditLog(
								KOALogHelper.ERROR,
								AuditEventListener.STATE_CHANGE,
								getSessionContext()
									.getCallerPrincipal()
									.getName(),
								this.getMessage(
									ErrorConstants
										.CHANGE_STATE_MESSAGE_ESB_FINGERPRINT_ERR,
									null));
						}
						String[] params = { "ESB" };
						KOALogHelper.logErrorCode(
							"ControllerBean.changeState",
							ErrorConstants.ERR_DIFF_FINGERPRINTS,
							params,
							null);
						/* return the right message */
						xCallResult.setResult(
							CallResult
								.NOTIFY_STATE_CHANGE_INVALID_FINGERPRINTS);
						xCallResult.setMessage(
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_MESSAGE_ESB_FINGERPRINT_ERR,
								null));
						bSetCallResult = false;
						//make sure the call result will not be set again
						bSuccess = false;
						sErrorMessage =
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_MESSAGE_ESB_FINGERPRINT_ERR,
								null);
						bFingerprintError = true;
					}
					/* check for the dynamic KR fingerprint */
					else if (
						koae.getErrorCode().equals(
							ErrorConstants.DYNAMIC_KR_FINGERPRINT_ERROR))
					{
						/* log the audit log */
						if (!bIsBlockingSystem)
						{
							this.logAuditLog(
								KOALogHelper.ERROR,
								AuditEventListener.STATE_CHANGE,
								getSessionContext()
									.getCallerPrincipal()
									.getName(),
								this.getMessage(
									ErrorConstants
										.CHANGE_STATE_MESSAGE_KR_DYN_FINGERPRINT_ERR,
									null));
						}
						String[] params = { "dynamic KR" };
						KOALogHelper.logErrorCode(
							"ControllerBean.changeState",
							ErrorConstants.ERR_DIFF_FINGERPRINTS,
							params,
							null);
						xCallResult.setResult(
							CallResult
								.NOTIFY_STATE_CHANGE_INVALID_FINGERPRINTS);
						xCallResult.setMessage(
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_MESSAGE_KR_DYN_FINGERPRINT_ERR,
								null));
						bSetCallResult = false;
						//make sure the call result will not be set again
						bSuccess = false;
						sErrorMessage =
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_MESSAGE_KR_DYN_FINGERPRINT_ERR,
								null);
						bFingerprintError = true;
					}
					/* check for the static KR fingerprint */
					else if (
						koae.getErrorCode().equals(
							ErrorConstants.STATIC_KR_FINGERPRINT_ERROR))
					{
						/* log the audit log */
						if (!bIsBlockingSystem)
						{
							this.logAuditLog(
								KOALogHelper.ERROR,
								AuditEventListener.STATE_CHANGE,
								getSessionContext()
									.getCallerPrincipal()
									.getName(),
								this.getMessage(
									ErrorConstants
										.CHANGE_STATE_MESSAGE_KR_STAT_FINGERPRINT_ERR,
									null));
						}
						String[] params = { "static KR" };
						KOALogHelper.logErrorCode(
							"ControllerBean.changeState",
							ErrorConstants.ERR_DIFF_FINGERPRINTS,
							params,
							null);
						xCallResult.setResult(
							CallResult
								.NOTIFY_STATE_CHANGE_INVALID_FINGERPRINTS);
						xCallResult.setMessage(
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_MESSAGE_KR_STAT_FINGERPRINT_ERR,
								null));
						bSetCallResult = false;
						//make sure the call result will not be set again
						bSuccess = false;
						sErrorMessage =
							this.getMessage(
								ErrorConstants
									.CHANGE_STATE_MESSAGE_KR_STAT_FINGERPRINT_ERR,
								null);
						bFingerprintError = true;
					}
					else
					{
						bSuccess = false;
						sErrorMessage =
							this.getMessage(
								koae.getErrorCode(),
								koae.getParameters());
						;
						bFingerprintError = false;
					}
				}
				catch (Exception e)
				{
					bSuccess = false;
					sErrorMessage = e.getMessage();
					bFingerprintError = false;
				}
			} // endif 			
			/* check the result */
			if (bSuccess)
			{
				if (xSubscription.getComponentType().equals(ComponentType.ESB))
				{
					bHasNotifiedESB = true;
				}
				else if (
					xSubscription.getComponentType().equals(ComponentType.KR))
				{
					bHasNotifiedKR = true;
				}
				/* log the audit log */
				if (!bIsBlockingSystem)
				{
					String[] saOK = { xSubscription.getComponentType()};
					this.logAuditLog(
						KOALogHelper.INFO,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_AUDIT_NOTIFY_COMPONENT_OK,
							saOK));
				}
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControllerBean.notifyAll] notifying component with JNDI "
						+ xSubscription.getJNDIName()
						+ " succesful");
			}
			else
			{
				bResult = false;
				xCallResult.addUnsuccesfullComponentType(
					xSubscription.getComponentType());
				if (xSubscription.getComponentType().equals(ComponentType.ESB)
					|| xSubscription.getComponentType().equals(ComponentType.KR))
				{
					if (!bFingerprintError)
					{
						bESBandKRresult = false;
						SubscriptionManager.setCommunicationFailed(
							xSubscription.getComponentID());
					}
				}
				else
				{
					SubscriptionManager.setCommunicationFailed(
						xSubscription.getComponentID());
				}
				/* log the audit log */
				if (!bIsBlockingSystem)
				{
					String[] saError =
						{ xSubscription.getComponentType(), sErrorMessage };
					this.logAuditLog(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						getSessionContext().getCallerPrincipal().getName(),
						this.getMessage(
							ErrorConstants
								.CHANGE_STATE_AUDIT_NOTIFY_COMPONENT_ERROR,
							saError));
				}
				KOALogHelper.logError(
					"ControllerBean.notifyAll",
					"Problem notifying component with JNDI "
						+ xSubscription.getJNDIName(),
					null);
			}
		}
		if (bResult)
		{
			xCallResult.setResult(CallResult.NOTIFY_STATE_CHANGE_SUCCESFUL);
		}
		else if (bSetCallResult)
		{
			/* if something went wrong, make a difference between 
			the ESB and KR that produced errors and the WSM and TSM */
			if (bESBandKRresult) //if ESB and KR went OK
			{
				xCallResult.setResult(CallResult.NOTIFY_STATE_CHANGE_WARNING);
			}
			else // if errors during notify of ESB and KR
				{
				xCallResult.setResult(CallResult.NOTIFY_STATE_CHANGE_ERROR);
			}
		}
		return xCallResult;
	}
	/**
	 * Gets the instance of the state entity bean.
	 * If there is no state entity bean, one will be created. 
	 * If a state entity bean can be found, this one is used.
	 * 
	 * @return Koa_state the Koa_state entity bean
	 * 
	 * @throws KOAException when something goes wrong getting the state entity bean
	 * 
	 */
	private Koa_state getStateEntity() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.getStateEntity] get state entity bean instance");
		Koa_state xState = null;
		xState = ObjectCache.getInstance().getState();
		return xState;
	}
	/**
	 * If no entity bean is found, a new one is created
	 * 
	 * @return Koa_state the newly created remote interface of the Koa_state entity bean
	 * 
	 * @throws KOAException an exception when something goes wrong during creation of the entity bean.
	 * 
	 */
	private Koa_state createNewStateEntity() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerBean.createNewStateEntity] start create new state");
		Koa_state xState = null;
		/* set the properties for the initial context */
		try
		{
			/* lookup the home interface of the state bean */
			Koa_stateHome xStateHome =
				ObjectCache.getInstance().getKOAStateHome();
			/* create the entity bean */
			xState = xStateHome.create(new Integer(0));
		}
		catch (CreateException ce)
		{
			String[] params = { "KOA state" };
			KOALogHelper.logErrorCode(
				"ControllerBean.createNewStateEntity",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.CONTROLLER_CREATE_STATE_ENTITY,
				ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "KOA state" };
			KOALogHelper.logErrorCode(
				"ControllerBean.createNewStateEntity",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.CONTROLLER_CREATE_STATE_ENTITY,
				re);
		}
		return xState;
	}
	/**
	 * open the ESB for counting the votes.
	 * 
	 * @param baPrivateKey The byte representation of the private key to use for opening
	 * @param sPassword The password used to encrypt the private key
	 * 
	 * @throws KOAException Exception during opening the ESB 
	 * 
	 */
	private void openESB(byte[] baPrivateKey, String sPassword)
		throws KOAException
	{
		/* set the properties for the initial context */
		try
		{
			/* lookup the home interface of the esb */
			ESBSessionEJBHome xESBHome =
				ObjectCache.getInstance().getESBSessionEJBHome();
			/* create the esb remote interface */
			ESBSessionEJB xESB = xESBHome.create();
			/* open the esb */
			xESB.openESB(baPrivateKey, sPassword);
		}
		catch (CreateException ce)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ControllerBean.openESB",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.CONTROLLER_OPEN_ESB, ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ControllerBean.openESB",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.CONTROLLER_OPEN_ESB, re);
		}
	}
	/**
	 * open the ESB for counting the votes.
	 * 
	 * @param baPrivateKey The byte representation of the private key to use for opening
	 * @param sPassword The password used to encrypt the private key
	 * 
	 * @throws KOAException Exception during opening the ESB 
	 * 
	 */
	private void countVotesOnESB() throws KOAException
	{
		/* set the properties for the initial context */
		try
		{
			/* lookup the home interface of the esb */
			ESBSessionEJBHome xESBHome =
				ObjectCache.getInstance().getESBSessionEJBHome();
			/* create the esb remote interface */
			ESBSessionEJB xESB = xESBHome.create();
			/* count the votes */
			xESB.telStemmen();
		}
		catch (CreateException ce)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ControllerBean.countVotesOnESB",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.CONTROLLER_BEAN_COUNT_VOTE_ESB,
				ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ControllerBean.countVotesOnESB",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.CONTROLLER_BEAN_COUNT_VOTE_ESB,
				re);
		}
	}
	/**
	 * Log the audit message
	 *  
	 * @param sActor The actor that is initializor of the logging
	 * @param sMessage The message to log
	 * 
	 */
	private void logAuditLog(
		int iType,
		String sAction,
		String sActor,
		String sMessage)
		throws KOAException
	{
		/* log to the audit log */
		try
		{
			/* set the properties for the initial context */
			UtilitySessionEJBHome home =
				ObjectCache.getInstance().getUtilityHome();
			UtilitySessionEJB utility = home.create();
			/* log the audit record */
			utility.logAuditRecord(
				iType,
				sAction,
				"Controller",
				sActor,
				sMessage);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "UtilitySessionEJB" };
			KOALogHelper.logErrorCode(
				"[ControllerBean.logAuditLog]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ERR_BLOCK_SYSTEM);
		}
		catch (javax.ejb.CreateException ce)
		{
			String[] params = { "UtilitySessionEJB" };
			KOALogHelper.logErrorCode(
				"[ControllerBean.logAuditLog]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.ERR_CREATE, params);
		}
	}
	private String getMessage(String code, String[] params)
	{
		String sMessage = "";
		try
		{
			sMessage =
				ErrorMessageFactory.getErrorMessageFactory().getErrorMessage(
					code,
					params);
		}
		catch (java.io.IOException ioe)
		{
			String[] saParams = { "ErrorMessageFactory" };
			KOALogHelper.logErrorCode(
				"ControllerBean.getMessage",
				ErrorConstants.ERR_IO,
				saParams,
				ioe);
			sMessage = "Kan melding met code " + code + " niet vinden.";
		}
		return sMessage;
	}
	/**
	 * Private method to hash a pincode so the incoming pincode
	 * can be compared to the saved pincode.
	 * 
	 * @param password The password to hash
	 * 
	 * @return String the hashed pincode
	 * 
	 * @throws Exception A general exception when something goes wrong hashing the pincode.
	 * 
	 */
	private String hashPinCode(String pincode) throws Exception
	{
		MessageDigest md = null;
		try
		{
			md = MessageDigest.getInstance("SHA-1");
			md.update(pincode.getBytes());
		}
		catch (java.security.NoSuchAlgorithmException nse)
		{
			throw new Exception("ENC-01");
		}
		byte[] output = md.digest();
		StringBuffer sb = new StringBuffer(2 * output.length);
		for (int i = 0; i < output.length; ++i)
		{
			int k = output[i] & 0xFF;
			if (k < 0x10)
				sb.append('0');
			sb.append(Integer.toHexString(k));
		}
		return sb.toString();
	}
}