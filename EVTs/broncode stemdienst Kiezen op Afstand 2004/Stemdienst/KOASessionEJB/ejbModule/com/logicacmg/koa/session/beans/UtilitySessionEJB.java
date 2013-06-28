/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.session.beans.UtilitySessionEJB
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
import com.logicacmg.koa.exception.KOAException;
/**
 * Remote interface for Enterprise Bean: UtilitySessionEJB
 */
public interface UtilitySessionEJB extends javax.ejb.EJBObject
{
	/**
	 * Logs the audit message to the database
	 * 
	 * @param sActor The actor initializating the logging
	 * @param sMessage The message to log
	 *  
	 */
	public void logAuditRecord(
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
		throws java.rmi.RemoteException, KOAException;
	public void logTXAuditRecord(
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
		throws KOAException, java.rmi.RemoteException;
}