/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.kieslijst.beans.KiesLijstHome.java
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
  *  0.1		18-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.kieslijst.beans;
/**
 * Home interface for Enterprise Bean: KiesLijst
 */
public interface KiesLijstHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: KiesLijst
	 */
	public com.logicacmg.koa.kieslijst.beans.KiesLijst create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
