/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.subscription.AbstractClientSubscription.java
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
import java.io.Serializable;

import com.logicacmg.koa.controller.subscription.ClientSubscription;
/**
 * Abstract class for the subscription data for the 
 * client. All default variables are in this class.
 * 
 * All the client subscription implementations can 
 * extend this class.
 * 
 * @author KuijerM
 * 
 */
public abstract class AbstractClientSubscription
	implements ClientSubscription, Serializable
{
	/**
	 * The unique component ID for the Client Subscription
	 * 
	 */
	protected String g_sComponentID = null;
	/**
	 * The component type for this subscription
	 * 
	 */
	protected String g_sComponentType = null;
	/**
	 * The JNDI name locating the module
	 * 
	 */
	protected String g_sJNDIName = null;
	/**
	 * The context for this subscription.
	 * This will only be filled if provided.
	 * 
	 */
	protected String g_sContext = null;
	/**
	 * The context factory for the initial context.
	 * This will only be filled if provided.
	 * 
	 */
	protected String g_sContextFactory = null;
	/**
	 * The constructor for the abstract client subscription class
	 * 
	 * @param sComponentID The ID of the component.
	 * @param sComponentType The component type for this subscription
	 * @param sJNDIName The JNDI name of the component
	 * @param sContext The context for the component, only used for ESB and KR
	 * 
	 */
	public AbstractClientSubscription(
		String sComponentID,
		String sComponentType,
		String sJNDIName,
		String sContext,
		String sContextFactory)
	{
		/* set the component id */
		this.g_sComponentID = sComponentID;
		/* set the component type */
		this.g_sComponentType = sComponentType;
		/* set the JDNI name */
		this.g_sJNDIName = sJNDIName;
		/* set the context */
		this.g_sContext = sContext;
		/* set the context factory */
		this.g_sContextFactory = sContextFactory;
	}
	/**
	 * Gets the unique identifier for this subscription
	 * 
	 * @return String the component ID
	 * 
	 */
	public String getComponentID()
	{
		return this.g_sComponentID;
	}
	/**
	 * Gets the component type for this subscription
	 * 
	 * @return String the component type
	 * 
	 */
	public String getComponentType()
	{
		return this.g_sComponentType;
	}
	/**
	 * Get the JNDI name for this subscription
	 * 
	 * @return String the JDNI name for this subscription
	 * 
	 */
	public String getJNDIName()
	{
		return this.g_sJNDIName;
	}
	/**
	 * The context for the subscription.
	 * This will only be filled when a context is provided.
	 * Else the context is null
	 * 
	 * @return String the context
	 * 
	 */
	public String getContext()
	{
		return this.g_sContext;
	}
	/**
	 * The context factory for the subscription.
	 * This will only be filled when a context factory is provided.
	 * Else the context factory is null
	 * 
	 * @return String the context factory
	 * 
	 */
	public String getContextFactory()
	{
		return this.g_sContextFactory;
	}
}
