/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.client.DefaultControlClient.java
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
  *  0.1		11-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.controller.client;
import java.rmi.RemoteException;
import java.util.Hashtable;
import javax.ejb.CreateException;
import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.controller.subscription.ClientSubscription;
import com.logicacmg.koa.controller.subscription.ControlClientSubscription;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.exception.KOAException;
/**
 * The default implementation of the control client.
 * This control client implementation is used for the 
 * RMI-communication and in combination with a ClientManager.
 * 
 * @author KuijerM
 * 
 */
public class DefaultControlClient
	extends AbstractControlClient
	implements ControlClient
{
	/* a collection of all the counters */
	private CounterData g_xCounterData;
	/**
	 * Constructor for the default implementation of the 
	 * control client
	 * 
	 * @param sComponentType The identifier of the component type
	 * 
	 * @throws KOAException General Exceptions
	 * 
	 */
	public DefaultControlClient(String sComponentType) throws Exception
	{
		/* call super constructor to set the componenttype */
		super(sComponentType);
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DefaultControlClient] Constructor for component "
				+ sComponentType);
	}
	/**
	 * Subscribes this control client at the controller
	 * 
	 * @throws KOAException if anything goes wrong during subscription.
	 * 
	 */
	public void subscribe() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DefaultControlClient.subscribe] subscribing component "
				+ g_sComponentType);
		/* execute the subscribe in the AbstractControlClient */
		super.subscribe();
		/* init the counters */
		g_xCounterData = new CounterData(g_sComponentType, g_sJNDIName);
	}
	/**
	 * Remote method to notify the control client that the  
	 * state has changed.
	 * 
	 * @return The boolean indicating if the update of the state was succesful
	 * 
	 * @throws RemoteException RMI Exception
	 * 
	 */
	public boolean notifyState(String sNewState) throws RemoteException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DefaultControlClient.notifyState] Component "
				+ g_sComponentType
				+ ", Controller notified new State "
				+ sNewState);
		super.g_sCurrentState = sNewState;
		return true;
	}
	/**
	 * Remote method to collect all the counters available 
	 * on this client
	 * 
	 * @return The counter data object with all the counters
	 * 
	 * @throws RemoteException RMI Exception
	 * 
	 */
	public CounterData collectCounters(int reason) throws RemoteException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DefaultControlClient.collectCounters] Component "
				+ g_sComponentType
				+ ", Collecting counter data");
		/* return the counter data */
		return g_xCounterData;
	}
	/**
	 * Add 1 for the counter for the specified counter key
	 * 
	 * @param sCounterKey The identifier for the key to update
	 * 
	 */
	public synchronized void updateCounter(String sCounterKey)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DefaultControlClient.updateCounter] Component "
				+ g_sComponentType
				+ ", Adding 1 to counter "
				+ sCounterKey);
		if (g_xCounterData != null)
		{
			/* update the counter directly on the counter data object */
			g_xCounterData.updateCounter(sCounterKey);
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[DefaultControlClient.updateCounter] Component not registered, cannot update counter");
		}
	}
	/**
	 * Resets the counter to zero for the counter for the specified counter key
	 * Only is executed when the counter does not have a value.
	 * 
	 * @param sCounterKey The identifier for the key to update
	 * 
	 */
	public synchronized void initializeCounter(String sCounterKey)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[DefaultControlClient.initializeCounter] Component "
				+ g_sComponentType
				+ ", counter reset to zero ");
		if (g_xCounterData != null)
		{
			/* update the counter directly on the counter data object */
			g_xCounterData.initializeCounter(sCounterKey);
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[DefaultControlClient.initializeCounter] Component not registered, cannot reset counter, counter data not found");
		}
	}
}