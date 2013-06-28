/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.client.AbstractControlClient.java
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

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.controller.client.ControlClient;
import com.logicacmg.koa.controller.subscription.ClientSubscription;
import com.logicacmg.koa.controller.subscription.ControlClientSubscription;
import com.logicacmg.koa.exception.KOAException;
/**
 * The abstract implementation of the control client
 * This abstract class is the base for all control client
 * implementations
 * 
 * @author KuijerM
 * 
 */
public abstract class AbstractControlClient
	extends PortableRemoteObject
	implements ControlClient
{
	/* The current state */
	protected String g_sCurrentState;
	/* The component type identifying the initiator 
		   of this component */
	protected String g_sComponentType;
	/* the identifier of this component */
	protected String g_sJNDIName = null;
	/**
	 * The contructor for the Abstract Control client
	 * 
	 * @param iComponentType The representation of the component type
	 * 
	 * @throws RemoteException Communication exception with the controller
	 * @throws Exception All general exceptions
	 * 
	 */
	public AbstractControlClient(String sComponentType)
		throws RemoteException, Exception
	{
		super();
		/* Set the component type for this control client */
		this.g_sComponentType = sComponentType;
		/* reset the status */
		g_sCurrentState = SystemState.UNKNOWN;
	}
	/**
	 * Get the current system state.
	 * This only returns the local state known by
	 * the control client. It does not get the 
	 * state from the controller.
	 * 
	 * @return The current State
	 * 
	 */
	public String getState()
	{
		/* return the local current state */
		return this.g_sCurrentState;
	}
	/**
	 * Abstract method to subscribe the control client 
	 * at the controller. All the control client objects
	 * must implement this method.
	 * 
	 */
	public void subscribe() throws KOAException
	{
		LogHelper.log(
			LogHelper.TRACE,
			"[AbstractControlClient.subscribe] subscribing component "
				+ g_sComponentType);
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
			/* look up the home interface */
			Object obj =
				icContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			ControllerHome xControllerHome =
				(ControllerHome) PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			/* create remote instance from the home interface */
			Controller xController = xControllerHome.create();
			LogHelper.log(
				LogHelper.TRACE,
				"[AbstractControlClient.subscribe] requesting jndi name for component");
			/* get the JNDI name used to subscribe */
			g_sJNDIName = xController.requestSubscription(g_sComponentType);
			/* subscribe the control client with this JNDI name */
			this.registerControlClient();
			LogHelper.log(
				LogHelper.TRACE,
				"[AbstractControlClient.subscribe] registration completed succesful, notifying controller");
			/* notify controller that subscription is complete */
			ClientSubscription xClient =
				new ControlClientSubscription(
					g_sComponentType,
					g_sJNDIName,
					JNDIProperties.getProperty(
						JNDIProperties.CONTROLLER_PROVIDER),
					JNDIProperties.getProperty(
						JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
			g_sCurrentState = xController.subscriptionComplete(xClient);
			LogHelper.log(
				LogHelper.TRACE,
				"[AbstractControlClient.subscribe] subscription completed succesful, got state "
					+ g_sCurrentState);
		}
		catch (CreateException ce)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.subscribe] create exception during lookup controller");
			ce.printStackTrace();
			throw new KOAException(ErrorConstants.CONTROL_CLIENT_SUBSCRIBE, ce);
		}
		catch (NamingException ne)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.subscribe] naming exception during lookup controller");
			ne.printStackTrace();
			throw new KOAException(ErrorConstants.CONTROL_CLIENT_SUBSCRIBE, ne);
		}
		catch (RemoteException re)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.subscribe] Remote exception during lookup controller");
			re.printStackTrace();
			throw new KOAException(ErrorConstants.CONTROL_CLIENT_SUBSCRIBE, re);
		}
	}
	/**
	 * Abstract method to unsubscribe the control client 
	 * at the controller. All the control client objects
	 * must implement this method.
	 * 
	 */
	public void unsubscribe() throws KOAException
	{
		LogHelper.log(
			LogHelper.TRACE,
			"[AbstractControlClient.unsubscribe] unsubscribing component "
				+ g_sComponentType);
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
			/* look up the home interface */
			Object obj =
				icContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			ControllerHome xControllerHome =
				(ControllerHome) PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			/* create remote instance from the home interface */
			Controller xController = xControllerHome.create();
			/* unsubscribe */
			xController.unsubscribe(this.g_sJNDIName);
		}
		catch (CreateException ce)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.unsubscribe] create exception during lookup controller");
			ce.printStackTrace();
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_UNSUBSCRIBE,
				ce);
		}
		catch (NamingException ne)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.unsubscribe] naming exception during lookup controller");
			ne.printStackTrace();
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_UNSUBSCRIBE,
				ne);
		}
		catch (RemoteException re)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.unsubscribe] Remote exception during lookup controller");
			re.printStackTrace();
			throw new KOAException(
				ErrorConstants.CONTROL_CLIENT_UNSUBSCRIBE,
				re);
		}
	}
	/**
	 * Register the control client in the JNDI of the controller
	 * 
	 * @param icContext The context representing the JNDI
	 * @param sJNDIName The JNDI name that is used to subscribe
	 * 
	 * @throws KOAException if anything goes wrong during subscription
	 * 
	 */
	private void registerControlClient() throws KOAException
	{
		LogHelper.log(
			LogHelper.TRACE,
			"[AbstractControlClient.registerControlClient] start subscribing with jndi name "
				+ g_sJNDIName);
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
		InitialContext icContext = null;
		try
		{
			/* create the initial context */
			icContext = new InitialContext(htProps);
			/* make sure the location in the jndi is free */
			icContext.unbind(g_sJNDIName);
			/* bind the control client to the jndi */
			icContext.bind(g_sJNDIName, this);
			LogHelper.log(
				LogHelper.TRACE,
				"[AbstractControlClient.registerControlClient] registration completed succesful");
		}
		catch (NamingException ne)
		{
			LogHelper.log(
				LogHelper.ERROR,
				"[AbstractControlClient.registerControlClient] error in registration of the control client");
			ne.printStackTrace();
			throw new KOAException(ErrorConstants.CONTROL_CLIENT_REGISTER, ne);
		}
		finally
		{
			/* always close the initial context */
			if (icContext != null)
			{
				try
				{
					icContext.close();
				}
				catch (Exception e)
				{
					LogHelper.log(
						LogHelper.ERROR,
						"[AbstractControlClient.registerControlClient] Could not close initial Context");
				}
			}
		}
	}
	/**
	 * Add one to the counter
	 * 
	 * @param sCounterKey The counter to update
	 * 
	 */
	public abstract void updateCounter(String sCounterKey);
	/**
	 * initialize the counter
	 * 
	 * @param sCounterKey The counter to update
	 * 
	 */
	public abstract void initializeCounter(String sCounterKey);
}