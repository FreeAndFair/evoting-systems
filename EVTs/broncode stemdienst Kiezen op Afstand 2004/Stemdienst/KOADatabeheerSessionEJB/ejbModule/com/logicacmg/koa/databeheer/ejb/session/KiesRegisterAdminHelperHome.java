/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperHome.java
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
  *  0.1		09-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.ejb.session;
/**
 * Home interface for Enterprise Bean: KiesRegisterAdminHelper
 */
public interface KiesRegisterAdminHelperHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: KiesRegisterAdminHelper
	 */
	public com
		.logicacmg
		.koa
		.databeheer
		.ejb
		.session
		.KiesRegisterAdminHelper create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}