/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHome.java
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
  *  1.0		09-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.ejb.session;
/**
 * Home interface for Enterprise Bean: KiesRegisterAdmin
 */
public interface KiesRegisterAdminHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: KiesRegisterAdmin
	 */
	public com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdmin create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
