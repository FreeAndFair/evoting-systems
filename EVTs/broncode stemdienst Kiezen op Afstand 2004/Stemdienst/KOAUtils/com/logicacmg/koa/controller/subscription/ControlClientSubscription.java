/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.subscription.ControlClientSubscription.java
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
package com.logicacmg.koa.controller.subscription;
import java.rmi.RemoteException;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.controller.SubscriptionManager;
import com.logicacmg.koa.controller.client.ControlClient;
import com.logicacmg.koa.controller.subscription.AbstractClientSubscription;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class for the subscription data for the 
 * control client. The controller recieves this object 
 * when the control client has finished subscribing to the controller.
 * This implementation is used for the WSM, TSM and Stemproces.
 * 
 * @author KuijerM
 * 
 */
public class ControlClientSubscription
	extends AbstractClientSubscription
	implements java.io.Serializable
{
	/**
	 * The constructor for the Control client subscription
	 * 
	 * @param sComponentType The component type for this component
	 * @param sJNDIName The JDNI name used to register this component.
	 * 
	 */
	public ControlClientSubscription(
		String sComponentType,
		String sJNDIName,
		String provider,
		String contextFactory)
	{
		super(sJNDIName, sComponentType, sJNDIName, provider, contextFactory);
	}
	/**
	 * Notify the control client that the state has changed
	 * 
	 * @param sCurrentState The current state the system is in
	 * @param sNewState the new state
	 * 
	 * @return boolean indicating the result of the notification.
	 * 
	 * @throws KOAException exception when something goes wrong during notify
	 * 
	 */
	public boolean notify(String sCurrentState, String sNewState)
		throws KOAException
	{
		boolean bResult = false;
		/* First check if communication has not failed for this loop */
		if (SubscriptionManager.getCommunicationFailed(this.getComponentID()))
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ControlClientSubscription.notify] Communication has failed during this loop earlier for the component with id "
					+ this.getComponentID()
					+ " not notifying new state...");
			return false;
		}
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(Context.INITIAL_CONTEXT_FACTORY, this.g_sContextFactory);
		htProps.put(Context.PROVIDER_URL, this.g_sContext);
		try
		{
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* look up the control client */
			Object obj = icContext.lookup(this.getJNDIName());
			ControlClient xControlClient =
				(ControlClient) PortableRemoteObject.narrow(
					obj,
					ControlClient.class);
			/* notify the control client of the state change */
			bResult = xControlClient.notifyState(sNewState);
			/* Check the result and throw error if !result */
			if (bResult)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControlClientSubscription.notify] notification succesful");
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[ControlClientSubscription.notify] notification failure");
				throw new KOAException(
					ErrorConstants.CONTROL_CLIENT_SUBSCRIPTION_NOTIFY);
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "ControlClient with id " + this.getJNDIName()};
			KOALogHelper.logErrorCode(
				"ControlClientSubscription.notify",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_SUBSCRIPTION_NOTIFY,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "ControlClient with id " + this.getJNDIName()};
			KOALogHelper.logErrorCode(
				"ControlClientSubscription.notify",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_SUBSCRIPTION_NOTIFY,
				re);
		}
		return bResult;
	}
	/**
	 * Get the counter data from the control client.
	 * 
	 * @return CounterData data object with the counter values.
	 * 
	 * @throws KOAException exception when something goes wrong collecting counters
	 * 
	 */
	public CounterData collectCounters(int reason) throws KOAException
	{
		CounterData xCounterData = null;
		/* First check if communication has not failed for this loop */
		if (SubscriptionManager.getCommunicationFailed(this.getComponentID()))
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ControlClientSubscription.collectCounters] Communication has failed during this loop earlier for the component with id "
					+ this.getComponentID()
					+ " not collecting counters...");
			return xCounterData;
		}
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
		try
		{
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* look up the control client */
			Object obj = icContext.lookup(this.getJNDIName());
			ControlClient xControlClient =
				(ControlClient) PortableRemoteObject.narrow(
					obj,
					ControlClient.class);
			/* notify the control client of the state change */
			xCounterData = xControlClient.collectCounters(reason);
			/* Check if the counterdata is filled for exception handling */
			if (xCounterData != null)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ControlClientSubscription.collectCounters] Collect counters succesful...");
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[ControlClientSubscription.collectCounters] Error in collecting counters...");
				throw new KOAException(
					ErrorConstants.CONTROL_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS);
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "ControlClient with id " + this.getJNDIName()};
			KOALogHelper.logErrorCode(
				"ControlClientSubscription.collectCounters",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "ControlClient with id " + this.getJNDIName()};
			KOALogHelper.logErrorCode(
				"ControlClientSubscription.collectCounters",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				re);
		}
		return xCounterData;
	}
}