/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.esb.beans.ESBSessionEJBHome
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
  *  0.1		14-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.esb.beans;
/**
 * Home interface for Enterprise Bean: KOAESBSessionEJB
 */
public interface ESBSessionEJBHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: KOAESBSessionEJB
	 */
	public com.logicacmg.koa.esb.beans.ESBSessionEJB create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
