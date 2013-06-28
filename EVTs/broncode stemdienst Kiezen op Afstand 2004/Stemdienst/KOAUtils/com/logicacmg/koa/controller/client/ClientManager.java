/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.client.ClientManager.java
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
  *  0.1		11-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.controller.client;
import java.rmi.RemoteException;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map;
import javax.ejb.CreateException;
import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;
import org.omg.CORBA.UNKNOWN;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * The client manager is a singleton object that is 
 * the manager for all the client control objects in 
 * the current JVM.
 * Through this manager object, all the client control
 * objects are singletons too.
 * 
 * @author KuijerM
 * 
 */
public class ClientManager
{
	/* the singleton instance of the client manager */
	private static ClientManager g_xInstance = null;
	/* hashtable containing all the client objects */
	private Map g_mClients;
	private ControllerHome g_xControllerHome = null;
	/**
	 * Private contructor for the client manager
	 * 
	 */
	private ClientManager()
	{
		super();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager] starting new client manager...");
		g_mClients = new HashMap();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager] getting controller home...");
		g_xControllerHome = ObjectCache.getInstance().getControllerHome();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager] got the controller home...");
	}
	/**
	 * Private static getter for the instance of 
	 * the client manger.
	 * All the static functions use this private getter.
	 * 
	 * @return The instance of the client manager
	 * 
	 */
	private static synchronized ClientManager getInstance()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.getInstance] get client Manager instance...");
		/* check if an instance is already present */
		if (g_xInstance == null)
		{
			/* if no instance is present, create new instance */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ClientManager.getInstance] creating new instance of the client manager...");
			g_xInstance = new ClientManager();
		}
		return g_xInstance;
	}
	/**
	 * subscribe the specified component at the controller.
	 * If the component is already subscribed, true is returned
	 * because this is correct.
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * 
	 * @throws KOAException when something goes wrong
	 */
	public synchronized static void subscribe(String sComponentKey)
		throws KOAException
	{
		/* call the corresponding method on the instance */
		getInstance().privateSubscribe(sComponentKey, null, null);
	}
	/**
	 * subscribe the specified component at the controller.
	 * If the component is already subscribed, true is returned
	 * because this is correct.
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * @param sIPAddress The ip address of the tel component's soap interface
	 * @param sIdentifier The identifier of the tel component's soap interface
	 * 
	 * @throws KOAException when something goes wrong
	 */
	public synchronized static void subscribe(
		String sComponentKey,
		String sIPAddress,
		String sIdentifier)
		throws KOAException
	{
		/* call the corresponding method on the instance */
		getInstance().privateSubscribe(sComponentKey, sIPAddress, sIdentifier);
	}
	/**
	 * unsubscribe the specified component from the controller.
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * 
	 * @throws KOAException when something goes wrong
	 */
	public synchronized static void unsubscribe(String sComponentKey)
		throws KOAException
	{
		getInstance().privateUnSubscribe(sComponentKey, null, null);
	}
	/**
	 * unsubscribe the specified component from the controller.
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * @param sIPAddress The ip address of the tel component's soap interface
	 * @param sIdentifier The identifier of the tel component's soap interface
	 * 
	 * @throws KOAException when something goes wrong
	 */
	public synchronized static void unsubscribe(
		String sComponentType,
		String sIPAddress,
		String sIdentifier)
		throws KOAException
	{
		getInstance().privateUnSubscribe(
			sComponentType,
			sIPAddress,
			sIdentifier);
	}
	/**
	 * Update the specified counter for the specified component.
	 * 
	 * @param sComponentKey The component type identifier to update
	 * @param sCounterKey The counter identifier to update the counter for
	 * 
	 */
	public synchronized static void updateCounter(
		String sComponentKey,
		String sCounterKey)
	{
		/* call the corresponding method on the instance */
		getInstance().privateUpdateCounter(sComponentKey, sCounterKey);
	}
	/**
	 * Sets the specified counter for the specified component type to zero.
	 * If the counter is already initialized, the counter will NOT be reset.
	 * 
	 * @param sComponentKey The component identifier
	 * @param sCounterKey The counter identifier
	 *  
	 */
	public synchronized static void initializeCounter(
		String sComponentKey,
		String sCounterKey)
	{
		/* call the corresponding method on the instance */
		getInstance().privateInitializeCounter(sComponentKey, sCounterKey);
	}
	/**
	 * Get the state known by the controller.
	 * 
	 * @return the current state
	 * 
	 * @throws KOAException Exception when no clients are subscribed and the state cannot be found
	 * 
	 */
	public synchronized static String getState() throws KOAException
	{
		/* call the corresponding method on the instance */
		return getInstance().privateGetState();
	}
	/**
	 * Get the state known by the specified component.
	 * 
	 * @param sComponentKey The component type identifier to get the state for
	 * 
	 * @return the current state
	 * 
	 */
	public synchronized static String getLocalState(String sComponentKey)
	{
		/* call the corresponding method on the instance */
		return getInstance().privateGetLocalState(sComponentKey);
	}
	/**
	 * Private method to update the specified counter for the specified component.
	 * 
	 * @param sComponentKey The component type identifier to update
	 * @param sCounterKey The counter identifier to update the counter for
	 * 
	 */
	private void privateUpdateCounter(String sComponentKey, String sCounterKey)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.updateCounter] for component "
				+ sComponentKey
				+ " update counter "
				+ sCounterKey
				+ "...");
		/* check if there is an instance */
		if (this.containsControlClient(sComponentKey))
		{
			/* get the instance of the control client */
			AbstractControlClient xClient =
				this.getControlClient(sComponentKey);
			/* update the counter for the counter key */
			if (xClient != null)
			{
				xClient.updateCounter(sCounterKey);
			}
			else
			{
				KOALogHelper.logError(
					"ClientManager.updateCounter",
					"Could not find control client, counter not updated.",
					null);
			}
		}
		else
		{
			KOALogHelper.logError(
				"ClientManager.updateCounter",
				"Could not find the control client for component type "
					+ sComponentKey
					+ ". Counter is not updated.",
				null);
		}
	}
	/**
	 * Private method to initialize the specified counter for the specified component type.
	 * 
	 * @param sComponentKey The component identifier
	 * @param sCounterKey The counter identifier
	 *  
	 */
	private void privateInitializeCounter(
		String sComponentType,
		String sCounterKey)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.privateInitializeCounter] for component "
				+ sComponentType
				+ " initializing counter "
				+ sCounterKey
				+ "...");
		/* check if there is an instance */
		if (this.containsControlClient(sComponentType))
		{
			/* get the instance of the control client */
			AbstractControlClient xClient =
				this.getControlClient(sComponentType);
			/* update the counter for the counter key */
			if (xClient != null)
			{
				xClient.initializeCounter(sCounterKey);
			}
			else
			{
				KOALogHelper.logError(
					"ClientManager.privateInitializeCounter",
					"Could not find control client, counter not initialized.",
					null);
			}
		}
		else
		{
			KOALogHelper.logError(
				"ClientManager.privateInitializeCounter",
				"Could not find the control client for component type "
					+ sComponentType
					+ ". Counter is not initialized.",
				null);
		}
	}
	/**
	 * Private method to get the state known by the controller in the EJB container.
	 * 
	 * @return the current state
	 * 
	 * @throws KOAException Exception when no clients are subscribed and the state cannot be found
	 * 
	 */
	private String privateGetState() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.getState] start getting state...");
		/* default set the state to unknown */
		String sCurrentState = SystemState.UNKNOWN;
		/* The state is asked at the controller, 
		because this is safer then using the first controlclient for this info */
		try
		{
			/* get the right state from the controller */
			Controller controller = g_xControllerHome.create();
			sCurrentState = controller.getCurrentState();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ClientManager.getState] returning state "
					+ sCurrentState
					+ "...");
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"ClientManager.getState",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.CLIENTMANAGER_GETSTATE, re);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"ClientManager.getState",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.CLIENTMANAGER_GETSTATE, ce);
		}
		catch (NullPointerException npe)
		{
			KOALogHelper.logErrorCode(
				"ClientManager.getState",
				ErrorConstants.ERR_NULL_POINTER,
				npe);
			throw new KOAException(ErrorConstants.CLIENTMANAGER_GETSTATE, npe);
		}
		/* return the right state from the controller */
		return sCurrentState;
	}
	/**
	 * Private method to get the state known by the specified component.
	 * 
	 * @param sComponentKey The component type identifier to get the state for
	 * 
	 * @return the current state
	 * 
	 */
	private String privateGetLocalState(String sComponentKey)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.getState] start getting state...");
		/* default set the state to unknown */
		String sCurrentState = SystemState.UNKNOWN;
		/* The state is asked locally for perfomance purposes  */
		/* get the right state */
		if (this.containsControlClient(sComponentKey))
		{
			sCurrentState = this.getControlClient(sComponentKey).getState();
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ClientManager.getLocalState] Could not find component with key "
					+ sComponentKey);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.getLocalState] returning local state "
				+ sCurrentState
				+ "...");
		/* return the right state from the controller */
		return sCurrentState;
	}
	/**
	 * private method to subscribe the specified component at the controller.
	 * If the component is already subscribed, true is returned
	 * because this is correct.
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * @param sIPAddress The ip address of the tsm component's SOAP interface
	 * @param sIdentifier The identifier of the tsm component's SOAP interface
	 * 
	 * @throws KOAException if something goes wrong
	 */
	private void privateSubscribe(
		String sComponentKey,
		String sIPAddress,
		String sIdentifier)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.subscribe] for component "
				+ sComponentKey
				+ " subscribing...");
		String sComponentID =
			this.getComponentID(sComponentKey, sIPAddress, sIdentifier);
		/* check if there is an instance */
		if (!this.containsControlClient(sComponentID))
		{
			try
			{
				/* if we dont have an instance, create new one */
				AbstractControlClient xClient = null;
				/* check what type it should be */
				if (sComponentKey.equals(ComponentType.TEL))
				{
					xClient =
						new SOAPControlClient(
							sComponentKey,
							sIPAddress,
							sIdentifier);
				}
				else
				{
					xClient = new DefaultControlClient(sComponentKey);
				}
				try
				{
					/* subscribe the new instance */
					xClient.subscribe();
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[ClientManager.subscribe] subscribing component "
							+ sComponentKey
							+ " succesful...");
					g_mClients.put(sComponentID, xClient);
				}
				catch (KOAException koae)
				{
					KOALogHelper.logError(
						"ClientManager.subscribe",
						"Client " + sComponentKey + " not subscribed.",
						koae);
					throw koae;
				}
			}
			/* if something goes wrong during subscription, log the error and return false */
			catch (Exception e)
			{
				String[] params =
					{ "Client " + sComponentKey + " not subscribed." };
				KOALogHelper.logErrorCode(
					"ClientManager.subscribe",
					ErrorConstants.ERR_CLIENT_ADD_SUBSCRIPTION,
					params,
					e);
				throw new KOAException(
					ErrorConstants.CLIENTMANAGER_SUBSCRIBE,
					e);
			}
		}
		/* if we dont have an instance, it is OK */
		else
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ClientManager.subscribe] Component already subscribed, cannot subscribe client "
					+ sComponentKey);
		}
	}
	/**
	 * private method to unsubscribe the specified component from the controller.
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * @param sIPAddress The ip address of the tsm component's SOAP interface, can be null
	 * @param sIdentifier The identifier of the tsm component's SOAP interface, can be null
	 * 
	 * @throws KOAException if something goes wrong
	 */
	private void privateUnSubscribe(
		String sComponentKey,
		String sIPAddress,
		String sIdentifier)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ClientManager.unsubscribe] for component "
				+ sComponentKey
				+ " removing subscription...");
		String sComponentID =
			this.getComponentID(sComponentKey, sIPAddress, sIdentifier);
		/* check if there is an instance */
		if (this.containsControlClient(sComponentID))
		{
			try
			{
				/* if we dont have an instance, create new one */
				AbstractControlClient xClient =
					this.getControlClient(sComponentID);
				try
				{
					/* subscribe the new instance */
					if (xClient != null)
					{
						xClient.unsubscribe();
						g_mClients.remove(sComponentID);
					}
					else
					{
						KOALogHelper.log(
							KOALogHelper.WARNING,
							"[ClientManager.unsubscribe] Client "
								+ sComponentKey
								+ " not unsubscribed.");
					}
				}
				catch (KOAException koae)
				{
					KOALogHelper.logError(
						"ClientManager.unsubscribe",
						"Client " + sComponentKey + " not unsubscribed.",
						koae);
					throw koae;
				}
			}
			/* if something goes wrong during subscription, log the error and return false */
			catch (Exception e)
			{
				String[] params =
					{ "Client " + sComponentKey + " not unsubscribed." };
				KOALogHelper.logErrorCode(
					"ClientManager.unsubscribe",
					ErrorConstants.ERR_CLIENT_REMOVE_SUBSCRIPTION,
					params,
					e);
				throw new KOAException(
					ErrorConstants.CLIENTMANAGER_UNSUBSCRIBE,
					e);
			}
		}
		/* if we dont have an instance, it is OK */
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ClientManager.unsubscribe] Component not subscribed, cannot unsubscribe client "
					+ sComponentKey);
		}
	}
	/**
	 * checks if the specified component type is already registrered at
	 * the controller.
	 * 
	 * @return boolean indicating the success (true) or failure (false) of the subscription
	 * 
	 */
	private boolean containsControlClient(String sComponentKey)
	{
		/* check if the component is in the list */
		return g_mClients != null
			&& !g_mClients.isEmpty()
			&& g_mClients.containsKey(sComponentKey);
	}
	/**
	 * Gets the instance of the default control client
	 * for the specified component type.
	 * 
	 * @param sComponentKey The component type identifier to get the instance for.
	 * 
	 * @return the instance of the control client.
	 * 
	 */
	private AbstractControlClient getControlClient(String sComponentKey)
	{
		AbstractControlClient xClient = null;
		/* check if the control client is in the list */
		if (this.containsControlClient(sComponentKey))
		{
			/* get the control client from the list */
			xClient = (AbstractControlClient) g_mClients.get(sComponentKey);
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ClientManager.getControlClient] Problem getting the Control Client for component "
					+ sComponentKey);
		}
		return xClient;
	}
	/**
	 * Private method to determine the name used to 
	 * save the specified component
	 * 
	 * @param sComponentKey The component type identifier to subscribe.
	 * @param sIPAddress The ip address of the tsm component's SOAP interface, can be null
	 * @param sIdentifier The identifier of the tsm component's SOAP interface, can be null
	 * 
	 */
	private String getComponentID(
		String sComponentType,
		String sIPAddress,
		String sIdentifier)
	{
		String sComponentID = sComponentType;
		/* default set the state to unknown */
		String sCurrentState = SystemState.UNKNOWN;
		if (sIPAddress != null && sIdentifier != null)
		{
			sComponentID = sComponentType + sIPAddress + sIdentifier;
		}
		return sComponentID;
	}
}