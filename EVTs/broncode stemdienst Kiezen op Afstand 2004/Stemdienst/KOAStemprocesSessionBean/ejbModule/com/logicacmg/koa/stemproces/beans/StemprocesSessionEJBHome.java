/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.stemproces.beans.StemprocesSessionEJBHome.java
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
  *  0.1		17-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.stemproces.beans;
/**
 * Home interface for Enterprise Bean: StemprocesSessionEJB
 */
public interface StemprocesSessionEJBHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: StemprocesSessionEJB
	 */
	public com.logicacmg.koa.stemproces.beans.StemprocesSessionEJB create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
