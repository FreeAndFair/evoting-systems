/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.session.beans.UtilitySessionEJBBean
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
  *  0.1		11-05-2003	MKu        	First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.session.beans;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.db.LoggingDB;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: UtilitySessionEJB
 * 
 * @author KuijerM
 * 
 */
public class UtilitySessionEJBBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	/**
	 * getSessionContext
	 */
	public javax.ejb.SessionContext getSessionContext()
	{
		return mySessionCtx;
	}
	/**
	 * setSessionContext
	 */
	public void setSessionContext(javax.ejb.SessionContext ctx)
	{
		mySessionCtx = ctx;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
	}
	/**
	 * ejbCreate
	 */
	public void ejbCreate() throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove()
	{
	}
	/**
	 * Log the audit record using the existing transaction
	 * 
	 */
	public void logTXAuditRecord(
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
		throws KOAException
	{
		this.privateLogAuditRecord(
			iSeverity,
			sAction,
			sComponent,
			sActor,
			sMessage);
	}
	/**
	 * Log the audit record using a new transaction
	 * 
	 */
	public void logAuditRecord(
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
		throws KOAException
	{
		this.privateLogAuditRecord(
			iSeverity,
			sAction,
			sComponent,
			sActor,
			sMessage);
	}
	/**
	 * Private method to log the audit message to the database
	 * 
	 * @param sActor The actor initializating the logging
	 * @param sMessage The message to log
	 *  
	 */
	private void privateLogAuditRecord(
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
		throws KOAException
	{
		try
		{
			/* log the audit row in the db */
			LoggingDB xLoggingDB = new LoggingDB();
			xLoggingDB.insertAuditRecord(
				iSeverity,
				sAction,
				sComponent,
				sActor,
				sMessage);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"UtilitySessionEJBBean.logAuditRecord",
				"cannot log the audit log to the database",
				koae);
			/* block system when audit log can not be updated */
			this.blockSystem();
			throw new KOAException(ErrorConstants.ERR_BLOCK_SYSTEM);
		}
		/* block system when audit log can not be updated */
		catch (Exception e)
		{
			KOALogHelper.logError(
				"UtilitySessionEJBBean.logAuditRecord",
				"cannot log the audit log to the database",
				e);
			this.blockSystem();
			throw new KOAException(ErrorConstants.ERR_BLOCK_SYSTEM);
		}
	}

	private void blockSystem()
	{
		KOALogHelper.logError(
			"UtilitySessionEJBBean.blockSystem",
			"Could not log to the audit database, blocking system...",
			null);
		try
		{
			ControllerHome home = ObjectCache.getInstance().getControllerHome();
			Controller controller = home.create();
			controller.block();
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[UtilitySessionEJBBean.blockSystem]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
		}
		catch (javax.ejb.CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[UtilitySessionEJBBean.blockSystem]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"KRSessionEJBBean.blockSystem",
				"KOAException during block of system, system not blocked",
				koae);
		}
		KOALogHelper.logError(
			"UtilitySessionEJBBean.blockSystem",
			"System blocked...",
			null);
	}
}