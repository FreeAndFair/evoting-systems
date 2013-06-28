/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.subscription.ClientSubscription.java
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

import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.exception.KOAException;
/**
 * interface for the subscription data for the 
 * client. The controller recieves this object 
 * when the client has finished subscribing to the controller.
 * 
 * @author KuijerM
 * 
 */
public interface ClientSubscription extends Serializable
{
	/**
	 * notify the new state to the corresponding client 
	 * 
	 * @param sCurrentState The current state of the system
	 * @param sNewState The new state
	 * 
	 * @return boolean indicating the success of the notification
	 * 
	 * @throws KOAException when something goes wrong during the notification
	 * 
	 */
	public boolean notify(String sCurrentState, String sNewState)
		throws KOAException;
	/**
	 * Collect the counters of the corresponding client 
	 * 
	 * @return CounterData The counter values
	 * 
	 * @throws KOAException when something goes wrong collecting the counters
	 * 
	 */
	public CounterData collectCounters(int reason) throws KOAException;
	/**
	 * Gets the unique identifier for this subscription
	 * 
	 * @return String the component ID
	 * 
	 */
	public String getComponentID();
	/**
	 * Get the JDNI name for this subscription
	 * 
	 * @return String the JDNI name used to register
	 * 
	 */
	public String getJNDIName();
	/**
	 * Gets the component type for this subscription
	 * 
	 * @return String the component type
	 * 
	 */
	public String getComponentType();
	/**
	 * Get the context for the subscription. Only should
	 * return a String when a context is providerd. 
	 * 
	 * @return String the context
	 * 
	 */
	public String getContext();
	/**
	 * Get the context factory for the subscription. Only should
	 * return a String when a context factory is providerd. 
	 * 
	 * @return String the context factory
	 * 
	 */
	public String getContextFactory();
}
