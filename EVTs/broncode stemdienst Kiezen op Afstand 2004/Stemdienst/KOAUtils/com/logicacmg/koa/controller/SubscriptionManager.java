/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.SubscriptionManager.java
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
package com.logicacmg.koa.controller;
import java.rmi.RemoteException;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.controller.subscription.ClientSubscription;
import com.logicacmg.koa.controller.subscription.ESBClientSubscription;
import com.logicacmg.koa.controller.subscription.KRClientSubscription;
import com.logicacmg.koa.db.ControllerDB;
import com.logicacmg.koa.esb.beans.ESBSessionEJB;
import com.logicacmg.koa.esb.beans.ESBSessionEJBHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kr.beans.KRSessionEJB;
import com.logicacmg.koa.kr.beans.KRSessionEJBHome;
import com.logicacmg.koa.utils.Convertor;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Subscription manager keeps a instance of the list with
 * all the subscribers of the controller. 
 * The subscription manager is a singleton that works 
 * together with the controller.
 * 
 * This class also keeps the list in sync with the database
 * 
 * @author KuijerM
 * 
 */
public class SubscriptionManager
{
	/**
	 * The instance of the subscription manager
	 * Needed for the singleton implementation.
	 * 
	 */
	private static SubscriptionManager g_xInstance = null;
	/**
	 * The list of subscribers
	 * 
	 */
	private Vector g_vSubscribers = null;
	/**
	 * Boolean indicating if the communication with the TSM has failed 
	 * in the scope of this state change. This boolean should always be
	 * reset before going through a change state.
	 * 
	 */
	private Vector g_vCommunicationFailed = null;
	/**
	 * Private constructor for the subscription manager
	 * 
	 * @throws KOAException When something goes wrong instantiating the Subscription manager
	 * 
	 */
	private SubscriptionManager() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager] constructor, initialising subscribers list");
		ControllerDB xControllerDB = new ControllerDB();
		/* create new instance */
		g_vSubscribers = new Vector();
		/* check if there are any subscribers in the database */
		if (TechnicalProps.isMultiNodeConfiguration()
			&& xControllerDB.getNumberOfSubscribers() > 0)
		{
			/* if the database is not empty, get the list from the db */
			g_vSubscribers = xControllerDB.getSubscribers();
		}
	}
	/**
	 * Private method to get the instance of the subscription 
	 * manager. Used for the Singleton pattern.
	 * 
	 */
	private static SubscriptionManager getInstance() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.getInstance] getting instance of SubscriptionManager");
		/* check if we have an instance */
		if (g_xInstance == null)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SubscriptionManager.getInstance] instance is null, creating new instance");
			//ControllerDB xControllerDB = new ControllerDB ();
			/* create a new instance */
			g_xInstance = new SubscriptionManager();
			try
			{
				/* check configuration for components */
				g_xInstance.checkConfiguredSubscriptions();
			}
			catch (KOAException koae)
			{
				KOALogHelper.logError(
					"SubscriptionManager.getInstance",
					"Could not subscribe ESB and KR configuration.. Configuration is corrupt",
					koae);
			}
		}
		/* return the instance */
		return g_xInstance;
	}
	/**
	 * Returns the client subscription for the specified component ID
	 * 
	 * @param sComponentID The component ID to get the client subscription for
	 * 
	 * @return ClientSubscription that corresponds to the specified ID.
	 * 
	 * @throws KOAException Exception when something goes wrong during this method
	 * 
	 */
	public synchronized static ClientSubscription getClientSubscription(String sComponentID)
		throws KOAException
	{
		return SubscriptionManager.getInstance().privateGetClientSubscription(
			sComponentID);
	}
	/**
	 * Adds the specified subscription to the list of subscribers.
	 * 
	 * @param xSubscription The subscription to add
	 * 
	 * @throws KOAException Exception when something goes wrong during this method
	 * 
	 */
	public synchronized static void addSubscriber(ClientSubscription xSubscription)
		throws KOAException
	{
		SubscriptionManager.getInstance().privateAddSubscriber(xSubscription);
	}
	/**
	 * Removes the subscription from the list of subscribers.
	 * 
	 * @param sComponentID the component id of the component to remove
	 * 
	 * @throws KOAException Exception when something goes wrong during this method
	 * 
	 */
	public synchronized static void removeSubscriber(String sComponentID)
		throws KOAException
	{
		SubscriptionManager.getInstance().privateRemoveSubscriber(sComponentID);
	}
	/**
	 * Returns the client subscription for the specified component ID
	 * 
	 * @param sComponentID The component ID to get the client subscription for
	 * 
	 * @return ClientSubscription that corresponds to the specified ID.
	 * 
	 * @throws KOAException Exception when something goes wrong during this method
	 * 
	 */
	private ClientSubscription privateGetClientSubscription(String sComponentID)
		throws KOAException
	{
		/* init variables */
		ClientSubscription xSubscr = null;
		ClientSubscription xSubscription = null;
		/* get all the subscribed components */
		Enumeration enumSubscribers = g_vSubscribers.elements();
		/* loop through all the subscriptions */
		while (enumSubscribers.hasMoreElements())
		{
			xSubscription = (ClientSubscription) enumSubscribers.nextElement();
			/* check if the subscription is the same */
			if (xSubscription.getComponentID().equals(sComponentID))
			{
				xSubscr = xSubscription;
				break;
			}
		}
		return xSubscr;
	}
	/**
	 * Add a subscriber to the list and to the database
	 * 
	 * @param xSubScription The client subscription 
	 * 
	 * @throws KOAException if something goes wrong during subscription
	 * 
	 */
	private void privateAddSubscriber(ClientSubscription xSubScription)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.addSubscriber] Adding subscription for component");
		if (xSubScription != null)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SubscriptionManager.addSubscriber] Adding subscription for component type "
					+ xSubScription.getComponentType()
					+ " with JDNI name "
					+ xSubScription.getJNDIName());
			try
			{
				/* add subscriber to the memory representation */
				g_vSubscribers.add(xSubScription);
				/* make sure the ordering of the subscribers is by priority */
				g_vSubscribers = this.orderItemsByPriority(g_vSubscribers);
				/* only add the subscription if it is a multinode config */
				if (TechnicalProps.isMultiNodeConfiguration())
				{
					/* add the subscriber to the database */
					ControllerDB xControllerDB = new ControllerDB();
					xControllerDB.addSubscription(xSubScription);
				}
			}
			catch (KOAException koae)
			{
				KOALogHelper.logError(
					"SubscriptionManager.addSubscriber",
					"KOAException thrown during subscription",
					koae);
				throw koae;
			}
			catch (Exception e)
			{
				KOALogHelper.logError(
					"SubscriptionManager.addSubscriber",
					"Could not complete subscription, subscriber could not be added",
					e);
				throw new KOAException(
					ErrorConstants.SUBSCRIPTIONMANAGER_ADD_SUBSCRIBER,
					e);
			}
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[SubscriptionManager.addSubscriber] Could not add subscription, because subscription is null");
		}
	}
	/**
	 * Removes a subscriber from the list and from the database
	 * 
	 * @param sComponentID The client subscription to remove
	 * 
	 * @throws KOAException if something goes wrong during subscription
	 * 
	 */
	private void privateRemoveSubscriber(String sComponentID)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.removeSubscriber] removing subscription component");
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
		/* search for the subscription in the list */
		ClientSubscription xSubScription =
			this.privateGetClientSubscription(sComponentID);
		/* check if we found a subscription */
		if (xSubScription == null)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[SubscriptionManager.removeSubscriber] component not found, can not remove subscription");
		}
		else
		{
			/* only remove the subscription if it is a multinode config */
			if (TechnicalProps.isMultiNodeConfiguration())
			{
				/* remove the subscription from the database */
				ControllerDB xControllerDB = new ControllerDB();
				xControllerDB.removeSubscription(sComponentID);
			}
			/* remove the subscription from the list */
			g_vSubscribers.remove(xSubScription);
			try
			{
				/* create the initial context */
				icContext = new InitialContext(htProps);
				/* remove the subscription from the JNDI tree */
				icContext.unbind(sComponentID);
			}
			catch (NamingException ne)
			{
				String[] params =
					{ "Subscriber in JNDI tree with name " + sComponentID };
				KOALogHelper.logErrorCode(
					"SubscriptionManager.removeSubscriber",
					ErrorConstants.ERR_NAMING,
					params,
					ne);
				throw new KOAException(
					ErrorConstants.SUBSCRIPTIONMANAGER_REMOVE_SUBSCRIBER,
					ne);
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
						KOALogHelper.log(
							KOALogHelper.WARNING,
							"Could not close initial Context");
					}
				}
			}
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SubscriptionManager.removeSubscriber] subscription removed succesfully");
		}
	}
	/**
	 * Get the list with all the subscribers.
	 * 
	 * @return Vector containing all Subscribers (ClientSubscription objects)
	 * 
	 * @throws KOAException exception when something went wrong getting the subscribers
	 */
	public synchronized static Vector getSubscribers() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.getSubscribers] Getting list with all subscriptions");
		ControllerDB xControllerDB = new ControllerDB();
		/* check if the list is in sync with the database */
		if (TechnicalProps.isMultiNodeConfiguration()
			&& xControllerDB.getNumberOfSubscribers()
				!= getInstance().g_vSubscribers.size())
		{
			/* if list is not in sync, get the list from the db */
			getInstance().g_vSubscribers = xControllerDB.getSubscribers();
		}
		/* return the list */
		return getInstance().g_vSubscribers;
	}
	/**
	 * Checks if the KR and ESB configuration files are already loaded.
	 * Should only be used in the constructor.
	 * 
	 * @throws KOAException When something goes wrong during checks
	 * 
	 */
	private void checkConfiguredSubscriptions() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.checkConfiguredSubscriptions] start check if all configured components are subscribed...");
		/* check subscriptions for ESB and LKR */
		this.checkConfiguredESBSubscriptions();
		this.checkConfiguredKRSubscriptions();
	}
	/**
	 * Checks if the ESB configuration is already loaded.
	 * Should only be used in checkConfiguredSubsciptions.
	 * 
	 * @throws KOAException When something goes wrong during checks
	 * 
	 */
	private void checkConfiguredESBSubscriptions() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.checkConfiguredESBSubscriptions] start check if all configured ESB components are subscribed...");
		ControllerDB xControllerDB = new ControllerDB();
		String sComponents = null;
		/* get the lists of configured ESB components */
		try
		{
			sComponents =
				JNDIProperties.getProperty(
					JNDIProperties.ESB_REGISTERED_COMPONENTS);
		}
		catch (KOAException koae)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[SubscriptionManager.checkConfiguredESBSubscriptions] no esb components found to subscribe...");
			return;
		}
		/* get the enumeration from the list */
		Convertor xConvertor = new Convertor();
		Enumeration enum =
			xConvertor.tokenizedStringToEnumeration(sComponents, ",");
		/* check each configuration if it is subscribed */
		String sComponent = null;
		while (enum.hasMoreElements())
		{
			sComponent = (String) enum.nextElement();
			/* if it is not subscribed in the controller, subscribe it */
			if (privateGetClientSubscription(sComponent) == null)
			{
				/* get the parameters from the properties */
				String sJNDIName =
					JNDIProperties.getProperty(
						JNDIProperties.ESB_REGISTERED_COMPONENT_JNDINAME_PREFIX
							+ sComponent);
				String sContext =
					JNDIProperties.getProperty(
						JNDIProperties.ESB_REGISTERED_COMPONENT_PROVIDER_PREFIX
							+ sComponent);
				String sContextFactory =
					JNDIProperties.getProperty(
						JNDIProperties
							.ESB_REGISTERED_COMPONENT_CONTEXT_FACTORY_PREFIX
							+ sComponent);
				try
				{
					/* set the propeties for the initial context */
					Hashtable htProps = new Hashtable();
					htProps.put(
						Context.INITIAL_CONTEXT_FACTORY,
						sContextFactory);
					htProps.put(Context.PROVIDER_URL, sContext);
					/* create the initial context */
					InitialContext icContext = new InitialContext(htProps);
					/* look up the home interface */
					Object obj = icContext.lookup(sJNDIName);
					ESBSessionEJBHome xHome =
						(ESBSessionEJBHome) PortableRemoteObject.narrow(
							obj,
							ESBSessionEJBHome.class);
					/* check if we can create a remote interface. */
					ESBSessionEJB xESB = xHome.create();
				}
				catch (NamingException ne)
				{
					String[] params = { "ESBSessionEJB" };
					KOALogHelper.logErrorCode(
						"SubscriptionManager.checkConfiguredESB",
						ErrorConstants.ERR_NAMING,
						params,
						ne);
					throw new KOAException(
						ErrorConstants.SUBSCRIPTIONMANAGER_ESB_SUBSCRIBER,
						ne);
				}
				catch (CreateException ce)
				{
					String[] params = { "ESBSessionEJB" };
					KOALogHelper.logErrorCode(
						"SubscriptionManager.checkConfiguredESB",
						ErrorConstants.ERR_CREATE,
						params,
						ce);
					throw new KOAException(
						ErrorConstants.SUBSCRIPTIONMANAGER_ESB_SUBSCRIBER,
						ce);
				}
				catch (RemoteException re)
				{
					String[] params = { "ESBSessionEJB" };
					KOALogHelper.logErrorCode(
						"SubscriptionManager.checkConfiguredESB",
						ErrorConstants.ERR_REMOTE,
						params,
						re);
					throw new KOAException(
						ErrorConstants.SUBSCRIPTIONMANAGER_ESB_SUBSCRIBER,
						re);
				}
				/* create new instance of ESB subscription */
				ClientSubscription xNewSubscr =
					new ESBClientSubscription(
						sComponent,
						sJNDIName,
						sContext,
						sContextFactory);
				/* add the subscription */
				this.privateAddSubscriber(xNewSubscr);
			}
		}
	}
	/**
	 * Checks if the KR configuration is already loaded.
	 * Should only be used in checkConfiguredSubsciptions.
	 * 
	 * @throws KOAException When something goes wrong during checks
	 * 
	 */
	private void checkConfiguredKRSubscriptions() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.checkConfiguredKRSubscriptions] start check if all configured KR components are subscribed...");
		ControllerDB xControllerDB = new ControllerDB();
		String sComponents = null;
		/* get the lists of configured KR components */
		try
		{
			sComponents =
				JNDIProperties.getProperty(
					JNDIProperties.KR_REGISTERED_COMPONENTS);
		}
		catch (KOAException koae)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[SubscriptionManager.checkConfiguredKRSubscriptions] no kr components found to subscribe...");
			return;
		}
		/* get the enumeration from the list */
		Convertor xConvertor = new Convertor();
		Enumeration enum =
			xConvertor.tokenizedStringToEnumeration(sComponents, ",");
		/* check each configuration if it is subscribed */
		String sComponent = null;
		while (enum.hasMoreElements())
		{
			sComponent = (String) enum.nextElement();
			/* if it is not subscribed in the controller, subscribe it */
			if (this.getClientSubscription(sComponent) == null)
			{
				/* get the parameters from the properties */
				String sJNDIName =
					JNDIProperties.getProperty(
						JNDIProperties.KR_REGISTERED_COMPONENT_JNDINAME_PREFIX
							+ sComponent);
				String sContext =
					JNDIProperties.getProperty(
						JNDIProperties.KR_REGISTERED_COMPONENT_PROVIDER_PREFIX
							+ sComponent);
				String sContextFactory =
					JNDIProperties.getProperty(
						JNDIProperties
							.KR_REGISTERED_COMPONENT_CONTEXT_FACTORY_PREFIX
							+ sComponent);
				try
				{
					/* set the propeties for the initial context */
					Hashtable htProps = new Hashtable();
					htProps.put(
						Context.INITIAL_CONTEXT_FACTORY,
						sContextFactory);
					htProps.put(Context.PROVIDER_URL, sContext);
					/* create the initial context */
					InitialContext icContext = new InitialContext(htProps);
					/* look up the home interface */
					Object obj = icContext.lookup(sJNDIName);
					KRSessionEJBHome xHome =
						(KRSessionEJBHome) PortableRemoteObject.narrow(
							obj,
							KRSessionEJBHome.class);
					/* check if we can create a remote interface. */
					KRSessionEJB xKR = xHome.create();
				}
				catch (NamingException ne)
				{
					String[] params = { "KRSessionEJB" };
					KOALogHelper.logErrorCode(
						"SubscriptionManager.checkConfiguredKR",
						ErrorConstants.ERR_NAMING,
						params,
						ne);
					throw new KOAException(
						ErrorConstants.SUBSCRIPTIONMANAGER_KR_SUBSCRIBER,
						ne);
				}
				catch (CreateException ce)
				{
					String[] params = { "KRSessionEJB" };
					KOALogHelper.logErrorCode(
						"SubscriptionManager.checkConfiguredKR",
						ErrorConstants.ERR_CREATE,
						params,
						ce);
					throw new KOAException(
						ErrorConstants.SUBSCRIPTIONMANAGER_KR_SUBSCRIBER,
						ce);
				}
				catch (RemoteException re)
				{
					String[] params = { "KRSessionEJB" };
					KOALogHelper.logErrorCode(
						"SubscriptionManager.checkConfiguredKR",
						ErrorConstants.ERR_REMOTE,
						params,
						re);
					throw new KOAException(
						ErrorConstants.SUBSCRIPTIONMANAGER_KR_SUBSCRIBER,
						re);
				}
				/* create new instance of KR subscription */
				ClientSubscription xNewSubscr =
					new KRClientSubscription(
						sComponent,
						sJNDIName,
						sContext,
						sContextFactory);
				/* add the subscription */
				this.privateAddSubscriber(xNewSubscr);
			}
		}
	}
	/**
	 * Method to order the items to the right priority
	 * 
	 * @param vUnsortedVector The unsorted vector containing all elements
	 * 
	 * @return Vector containing the sorted list of all items
	 * 
	 */
	private Vector orderItemsByPriority(Vector vUnsortedVector)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.orderItemsByPriority] start ordering items based on priority of notification...");
		Vector vResult = new Vector();
		ClientSubscription xSubscription = null;
		/* extract all the Web components, because Web has highest priority */
		for (int i = 0; i < vUnsortedVector.size(); i++)
		{
			xSubscription = (ClientSubscription) vUnsortedVector.elementAt(i);
			if (xSubscription.getComponentType().equals(ComponentType.WEB))
			{
				vResult.add(xSubscription);
			}
		}
		/* extract all the Tel components, because tel has priority 2 */
		for (int i = 0; i < vUnsortedVector.size(); i++)
		{
			xSubscription = (ClientSubscription) vUnsortedVector.elementAt(i);
			if (xSubscription.getComponentType().equals(ComponentType.TEL))
			{
				vResult.add(xSubscription);
			}
		}
		/* extract all the Stem components, because STEM has priority 3 */
		for (int i = 0; i < vUnsortedVector.size(); i++)
		{
			xSubscription = (ClientSubscription) vUnsortedVector.elementAt(i);
			if (xSubscription.getComponentType().equals(ComponentType.STEM))
			{
				vResult.add(xSubscription);
			}
		}
		/* extract all the KR components, because KR has priority 4 */
		for (int i = 0; i < vUnsortedVector.size(); i++)
		{
			xSubscription = (ClientSubscription) vUnsortedVector.elementAt(i);
			if (xSubscription.getComponentType().equals(ComponentType.KR))
			{
				vResult.add(xSubscription);
			}
		}
		/* extract all the ESB components, because KR has priority 5 */
		for (int i = 0; i < vUnsortedVector.size(); i++)
		{
			xSubscription = (ClientSubscription) vUnsortedVector.elementAt(i);
			if (xSubscription.getComponentType().equals(ComponentType.ESB))
			{
				vResult.add(xSubscription);
			}
		}
		return vResult;
	}
	/**
	 * Static method to reset the communication with the components, 
	 * so we have a clean start before the state change.
	 * 
	 * 
	 */
	public static void resetCommunicationFailed()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.resetCommunicationFailed] reset communication failure list");
		/* reset the indicating if the communication
		with the components has failed */
		try
		{
			getInstance().g_vCommunicationFailed = null;
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SubscriptionManager.resetCommunicationFailed",
				"Could not reset the vector with communication failures...",
				koae);
		}
	}
	/**
	 * Static method to set the communication failed flag to true for a component.
	 * The communication has failed with the component if this method is called.
	 * 
	 * @param sComponent The component that has failed communication
	 * 
	 */
	public static void setCommunicationFailed(String sComponent)
	{
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"[SubscriptionManager.setCommunicationFailed] communication has failed in this loop for component with ID "
				+ sComponent);
		try
		{
			/* check if the vector is null, create new one if so */
			if (getInstance().g_vCommunicationFailed == null)
			{
				getInstance().g_vCommunicationFailed = new Vector();
			}
			/* add the component for which the communication has failed */
			getInstance().g_vCommunicationFailed.add(sComponent);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SubscriptionManager.setCommunicationFailed",
				"Could not set the communication failure for component "
					+ sComponent
					+ "...",
				koae);
		}
	}
	/**
	 * Gets the boolean indicating if the communication with
	 * the given component has failed or not.
	 * 'true' indicates the communication has failed.
	 * 'false' indicates the communication has not failed
	 * 
	 * @param sComponent The component to check for failed communication
	 * 
	 * @return boolean indicatin if the TSM has failed. 'true' indicates the communication has failed. 'false' indicates the communication has not failed.
	 */
	public static boolean getCommunicationFailed(String sComponent)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SubscriptionManager.getCommunicationFailed] check if communication failed before in this loop for component with ID "
				+ sComponent);
		boolean bFound = false;
		try
		{
			/* if the list is null, there are no components with failed communication */
			if (getInstance().g_vCommunicationFailed == null)
			{
				return false;
			}
			String sTempComp = null;
			/* loop through the vector in search for the given component */
			Vector vLocal = getInstance().g_vCommunicationFailed;
			for (int i = 0; i < vLocal.size() && !bFound; i++)
			{
				sTempComp = (String) vLocal.elementAt(i);
				if (sTempComp.equals(sComponent))
				{
					KOALogHelper.log(
						KOALogHelper.ERROR,
						"[SubscriptionManager.getCommunicationFailed] found communication error for component with ID "
							+ sComponent);
					bFound = true;
					break;
				}
			}
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SubscriptionManager.getCommunicationFailed",
				"Could not get the communication failure for component "
					+ sComponent
					+ "...",
				koae);
		}
		return bFound;
	}
}