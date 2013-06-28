/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.beans.ControllerHome.java
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
package com.logicacmg.koa.controller.beans;
/**
 * Home interface for Enterprise Bean: Controller
 */
public interface ControllerHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: Controller
	 */
	public com.logicacmg.koa.controller.beans.Controller create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
