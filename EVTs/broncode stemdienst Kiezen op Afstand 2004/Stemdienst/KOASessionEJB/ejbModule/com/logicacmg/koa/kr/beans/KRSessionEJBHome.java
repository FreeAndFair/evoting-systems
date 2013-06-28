/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.kr.beans.KRSessionEJBHome
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
  *  0.1		11-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.kr.beans;
/**
 * Home interface for Enterprise Bean: KRSessionEJB
 */
public interface KRSessionEJBHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: KRSessionEJB
	 */
	public com.logicacmg.koa.kr.beans.KRSessionEJB create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
