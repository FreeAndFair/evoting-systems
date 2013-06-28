/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.client.ControlClient.java
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
import java.rmi.Remote;
import java.rmi.RemoteException;

import com.logicacmg.koa.dataobjects.CounterData;
/**
 * Remote interface for all control clients for
 * communication between controller and clients.
 * 
 * @author KuijerM
 * 
 */
public interface ControlClient extends Remote
{
	/**
	 * In case of state changes, the controller
	 * informes all the clients of the state change
	 * through this method.
	 * 
	 */
	public boolean notifyState(String sNewState) throws RemoteException;
	/**
	 * Collect all the counters on the client side.
	 * This method is initialized by the controller.
	 * 
	 */
	public CounterData collectCounters(int reason) throws RemoteException;
}