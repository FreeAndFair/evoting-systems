/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.subscription.ESBClientSubscription.java
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

import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.controller.subscription.AbstractClientSubscription;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.esb.beans.ESBSessionEJB;
import com.logicacmg.koa.esb.beans.ESBSessionEJBHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class for the subscription data for the 
 * ESB client. The controller recieves this object 
 * when the control client has finished subscribing to the controller.
 * This implementation is used for the ESB.
 * 
 * @author KuijerM
 * 
 */
public class ESBClientSubscription
	extends AbstractClientSubscription
	implements java.io.Serializable
{
	/**
	 * The constructor for the ESB client subscription
	 * 
	 * @param sComponentID The unique identifier for the component. For internal use only
	 * @param sJNDIName The JNDI name locating the ESB module
	 * @param sContext The context to use to locate the ESB Module
	 * 
	 */
	public ESBClientSubscription(
		String sComponentID,
		String sJNDIName,
		String sContext,
		String sContextFactory)
	{
		/* set the component type */
		super(
			sComponentID,
			ComponentType.ESB,
			sJNDIName,
			sContext,
			sContextFactory);
	}
	/**
	 * Notify the ESB module that the state has changed
	 * 
	 * @param sNewState the new state
	 * 
	 * @return boolean indicating the result of the notification.
	 * 
	 * @throws KOAException when something goes wrong during notification
	 * 
	 */
	public boolean notify(String sCurrentState, String sNewState)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ESBClientSubscription.notify] notify ESB with state "
				+ sNewState);
		boolean bResult = false;
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(Context.INITIAL_CONTEXT_FACTORY, g_sContextFactory);
		htProps.put(Context.PROVIDER_URL, g_sContext);
		try
		{
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* look up the ESB session bean */
			Object obj = icContext.lookup(g_sJNDIName);
			ESBSessionEJBHome xESBSessionEJBHome =
				(ESBSessionEJBHome) PortableRemoteObject.narrow(
					obj,
					ESBSessionEJBHome.class);
			ESBSessionEJB xESBSessionEJB = xESBSessionEJBHome.create();
			/* notify the ESB bean */
			xESBSessionEJB.changeState(sCurrentState, sNewState);
			bResult = true;
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ESBClientSubscription.notify] notification succesful");
		}
		catch (CreateException ce)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ESBClientSubscription.notify",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.ESB_CLIENT_SUBSCRIPTION_NOTIFY,
				ce);
		}
		catch (NamingException ne)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ESBClientSubscription.notify",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(
				ErrorConstants.ESB_CLIENT_SUBSCRIPTION_NOTIFY,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ESBClientSubscription.notify",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.ESB_CLIENT_SUBSCRIPTION_NOTIFY,
				re);
		}
		return bResult;
	}
	/**
	 * Get the counter data from the ESB module.
	 * 
	 * @return CounterData data object with the counter values.
	 * 
	 * @throws KOAException when something goes wrong during collection of counters
	 * 
	 */
	public CounterData collectCounters(int reason) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ESBClientSubscription.collectCounters] collecting counters for ESB "
				+ g_sComponentID);
		CounterData xCounterData = null;
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(Context.INITIAL_CONTEXT_FACTORY, g_sContextFactory);
		htProps.put(Context.PROVIDER_URL, g_sContext);
		try
		{
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* look up the ESB session bean */
			Object obj = icContext.lookup(g_sJNDIName);
			ESBSessionEJBHome xESBSessionEJBHome =
				(ESBSessionEJBHome) PortableRemoteObject.narrow(
					obj,
					ESBSessionEJBHome.class);
			ESBSessionEJB xESBSessionEJB = xESBSessionEJBHome.create();
			/* collect the counters */
			xCounterData = xESBSessionEJB.collectCounters(g_sComponentID);
		}
		catch (CreateException ce)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ESBClientSubscription.collectCounters",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.ESB_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				ce);
		}
		catch (NamingException ne)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ESBClientSubscription.collectCounters",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(
				ErrorConstants.ESB_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "ESBSessionEJB" };
			KOALogHelper.logErrorCode(
				"ESBClientSubscription.collectCounters",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.ESB_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				re);
		}
		return xCounterData;
	}
}