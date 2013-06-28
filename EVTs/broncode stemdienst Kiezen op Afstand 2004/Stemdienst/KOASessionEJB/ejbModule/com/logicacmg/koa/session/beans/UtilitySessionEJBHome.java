/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.session.beans.UtilitySessionEJBHome
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
  *  0.1		11-05-2003	MKu        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.session.beans;
/**
 * Home interface for Enterprise Bean: UtilitySessionEJB
 */
public interface UtilitySessionEJBHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: UtilitySessionEJB
	 */
	public com.logicacmg.koa.session.beans.UtilitySessionEJB create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
