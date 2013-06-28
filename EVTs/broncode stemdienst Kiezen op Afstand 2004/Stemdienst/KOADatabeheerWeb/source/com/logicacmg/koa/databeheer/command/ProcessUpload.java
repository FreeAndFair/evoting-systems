/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.bean.KieslijstUpload.java
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
package com.logicacmg.koa.databeheer.command;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;

import com.logica.eplatform.command.AbstractTargetableCommand;
import com.logica.eplatform.command.CommandException;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.scheduler.JobContext;
import com.logicacmg.koa.scheduler.SchedulerConstants;
import com.logicacmg.koa.scheduler.beans.SchedulerAdmin;
import com.logicacmg.koa.scheduler.beans.SchedulerAdminHome;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * This class will process the YES/NO in the report 
 * if yes it will process the tempdata 
 * if no it will remove the tempdata
 * for both the KieslijstAdmin and the KiesRegisterAdmin
 */
public class ProcessUpload
	extends AbstractTargetableCommand
	implements HttpCommand
{
	// const. 	
	private final String JA = "JA";
	private final String NEE = "NEE";
	private final String PROCESS = "process";
	private final String KIESLIJST = "kieslijst";
	private final String INDEX_PAGE = "index.jsp";
	private final String COMMIT_RESULT_PAGE = "uploadcommitmessage.jsp";
	private final String ERROR_PAGE = "error.jsp";
	// menbers
	private boolean bProcess;
	private boolean bKieslijst;
	private int iTempDataID;
	/**
	 * This methode is executed by the Command taget in the EJB container.
	 * It starts the KieslijstAdmin or the KiesRegisterAdmin
	 * @see AbstractTargetableCommand#execute()
	 */
	public void execute() throws CommandException, EPlatformException
	{
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.SCHEDULER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.SCHEDULER_PROVIDER));
		try
		{
			InitialContext ic = new InitialContext(htProps);
			Object obj =
				ic.lookup(
					JNDIProperties.getProperty(
						JNDIProperties.SCHEDULER_ADMIN_JNDI_NAME));
			SchedulerAdminHome home =
				(SchedulerAdminHome) javax.rmi.PortableRemoteObject.narrow(
					obj,
					SchedulerAdminHome.class);
			SchedulerAdmin bean = home.create();
			JobContext context = new JobContext();
			context.setProperty(
				SchedulerConstants.TEMP_DATA_ID_KEY,
				Integer.toString(iTempDataID));
			if (bKieslijst)
			{
				if (bProcess)
				{
					KOALogHelper.log(
						LogHelper.INFO,
						"[ProcessUpload] start process import kieslijst");
					BigDecimal bdJobType =
						new BigDecimal(
							Long.parseLong(
								SchedulerConstants
									.JOB_TYPE_ID_IMPORT_KIES_LIJST));
					bean.rescheduleForJobType(
						bdJobType,
						context.getXMLString());
				}
				else
				{
					KOALogHelper.log(
						LogHelper.INFO,
						"[ProcessUpload] start remove import kieslijst");
					BigDecimal bdJobType =
						new BigDecimal(
							Long.parseLong(
								SchedulerConstants
									.JOB_TYPE_ID_REMOVE_KIES_LIJST));
					bean.rescheduleForJobType(
						bdJobType,
						context.getXMLString());
				}
			}
			else
			{
				if (bProcess)
				{
					KOALogHelper.log(
						LogHelper.INFO,
						"[ProcessUpload] start process import kies register");
					BigDecimal bdJobType =
						new BigDecimal(
							Long.parseLong(
								SchedulerConstants
									.JOB_TYPE_ID_IMPORT_KIES_REGISTER));
					bean.rescheduleForJobType(
						bdJobType,
						context.getXMLString());
				}
				else
				{
					KOALogHelper.log(
						LogHelper.INFO,
						"[ProcessUpload] start remove import kies register");
					BigDecimal bdJobType =
						new BigDecimal(
							Long.parseLong(
								SchedulerConstants
									.JOB_TYPE_ID_REMOVE_KIES_REGISTER));
					bean.rescheduleForJobType(
						bdJobType,
						context.getXMLString());
				}
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "SchedulerAdmin" };
			KOALogHelper.logErrorCode(
				"ProcessUpload",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "SchedulerAdmin" };
			KOALogHelper.logErrorCode(
				"ProcessUpload",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				re);
		}
		catch (CreateException ce)
		{
			String[] params = { "SchedulerAdmin" };
			KOALogHelper.logErrorCode(
				"ProcessUpload",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ce);
		}
	}
	/**
	 * Not used
	 * @see HttpCommand#getErrorJSP()
	 */
	public String getErrorJSP()
	{
		return ERROR_PAGE;
	}
	/**
	 * Not used
	 * @see HttpCommand#getResultJSP()
	 */
	public String getResultJSP()
	{
		if (this.bProcess)
		{
			return COMMIT_RESULT_PAGE;
		}
		else
		{
			return INDEX_PAGE;
		}
	}
	/**
	 * this mehtode gets the parameters from the session 
	 * these parameters are used in the execute methode
	 * 
	 * @see HttpCommand#init(HttpServletRequest)
	 * @param xReq The HttpServletRequest
	 */
	public void init(HttpServletRequest xReq) throws EPlatformException
	{
		KOALogHelper.audit(
			KOALogHelper.INFO,
			"ProcessUpload",
			AuditEventListener.DATA_MANAGEMENT,
			xReq.getUserPrincipal().getName(),
			"ProcessUpload started");
		KOALogHelper.log(
			LogHelper.INFO,
			"[ProcessUpload] ProcessUpload started");
		String sProcess = xReq.getParameter(PROCESS);
		if (sProcess.trim().equals(JA))
		{
			bProcess = true;
		}
		else
		{
			bProcess = false;
		}
		HttpSession xSession = xReq.getSession();
		// get param from session
		iTempDataID =
			Integer.parseInt(
				(String) xSession.getAttribute(
					CommandConstants.UPLOAD_SESSION));
		//xSession.getAttribute(CommandConstants.UPLOAD_ACTION);
		String sType =
			(String) xSession.getAttribute(CommandConstants.UPLOAD_CONTENTTYPE);
		if (sType.trim().equals(KIESLIJST))
		{
			bKieslijst = true;
		}
		else
		{
			bKieslijst = false;
		}
		KOALogHelper.log(LogHelper.INFO, "[ProcessUpload] Upload param OK");
	}
	/**
	 * Not used
	 * @see HttpCommand#updateSession(HttpSession)
	 */
	public void updateSession(HttpSession xSession) throws EPlatformException
	{
	}
}