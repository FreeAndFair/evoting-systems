/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.subscription.KRClientSubscription.java
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
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kr.beans.KRSessionEJB;
import com.logicacmg.koa.kr.beans.KRSessionEJBHome;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class for the subscription data for the 
 * KR client. The controller recieves this object 
 * when the control client has finished subscribing to the controller.
 * This implementation is used for the KR.
 * 
 * @author KuijerM
 * 
 */
public class KRClientSubscription
	extends AbstractClientSubscription
	implements java.io.Serializable
{
	/**
	 * The constructor for the KR client subscription
	 * 
	 * @param sComponentID the unique identifier for this component, only for internal use
	 * @param sJNDIName The JNDI name locating the KR module
	 * @param sContext The context to use to locate the KR Module
	 * 
	 */
	public KRClientSubscription(
		String sComponentID,
		String sJNDIName,
		String sContext,
		String sContextFactory)
	{
		/* set the component type */
		super(
			sComponentID,
			ComponentType.KR,
			sJNDIName,
			sContext,
			sContextFactory);
	}
	/**
	 * Notify the KR module that the state has changed
	 * 
	 * @param sCurrentState The current state the system is in
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
			"[KRClientSubscription.notify] notify KR with state " + sNewState);
		boolean bResult = false;
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(Context.INITIAL_CONTEXT_FACTORY, g_sContextFactory);
		htProps.put(Context.PROVIDER_URL, g_sContext);
		try
		{
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* look up the KR session bean */
			Object obj = icContext.lookup(g_sJNDIName);
			KRSessionEJBHome xKRSessionEJBHome =
				(KRSessionEJBHome) PortableRemoteObject.narrow(
					obj,
					KRSessionEJBHome.class);
			KRSessionEJB xKRSessionEJB = xKRSessionEJBHome.create();
			/* notify the ESB bean */
			xKRSessionEJB.changeState(sCurrentState, sNewState);
			bResult = true;
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KRClientSubscription.notify] notification succesful");
		}
		catch (CreateException ce)
		{
			String[] params = { "KRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KRClientSubscription.notify",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.KR_CLIENT_SUBSCRIPTION_NOTIFY,
				ce);
		}
		catch (NamingException ne)
		{
			String[] params = { "KRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KRClientSubscription.notify",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(
				ErrorConstants.KR_CLIENT_SUBSCRIPTION_NOTIFY,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "KRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KRClientSubscription.notify",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.KR_CLIENT_SUBSCRIPTION_NOTIFY,
				re);
		}
		return bResult;
	}
	/**
	 * Get the counter data from the KR module.
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
			"[KRClientSubscription.collectCounters] collecting counters for KR "
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
			/* look up the KR session bean */
			Object obj = icContext.lookup(g_sJNDIName);
			KRSessionEJBHome xKRSessionEJBHome =
				(KRSessionEJBHome) PortableRemoteObject.narrow(
					obj,
					KRSessionEJBHome.class);
			KRSessionEJB xKRSessionEJB = xKRSessionEJBHome.create();
			/* collect the counters */
			xCounterData = xKRSessionEJB.collectCounters(g_sComponentID);
		}
		catch (CreateException ce)
		{
			String[] params = { "xKRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KRClientSubscription.collectCounters",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.KR_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				ce);
		}
		catch (NamingException ne)
		{
			String[] params = { "xKRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KRClientSubscription.collectCounters",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(
				ErrorConstants.KR_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "xKRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KRClientSubscription.collectCounters",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.KR_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS,
				re);
		}
		return xCounterData;
	}
}
