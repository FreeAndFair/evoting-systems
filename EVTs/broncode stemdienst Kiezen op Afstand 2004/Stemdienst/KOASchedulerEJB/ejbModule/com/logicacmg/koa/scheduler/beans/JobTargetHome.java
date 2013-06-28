/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.beans.JobTargetHome.java
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
  *  0.1		15-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler.beans;
/**
 * Home interface for Enterprise Bean: JobTarget
 */
public interface JobTargetHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: JobTarget
	 */
	public com.logicacmg.koa.scheduler.beans.JobTarget create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
