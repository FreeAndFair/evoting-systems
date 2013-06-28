/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.CloseCommand.java
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
  *  0.1		01-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.voorzitter.command.statechange;
import java.rmi.RemoteException;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.voorzitter.command.statechange.AbstractStateChangeCommand;
/**
 * Change state to closed.
 * 
 * @author KuijerM
 * 
 */
public class CloseCommand extends AbstractStateChangeCommand
{
	private String g_sUser = null;
	/**
	 * The execute method on the Close command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of the Controller can not be created.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.log(LogHelper.INFO, "[CloseCommand.exeute] execute ");
		boolean bBackupFailed = false;
		String sMessage = null;
		try
		{
			/* init the variabeles */
			Hashtable htProps = new Hashtable();
			htProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
			htProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
			/* init the context */
			InitialContext icContext = new InitialContext(htProps);
			/* lookup the controller */
			Object obj =
				icContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			/* create the controller */
			ControllerHome xControllerHome =
				(ControllerHome) PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			Controller xController = xControllerHome.create();
			// Verify pincodes. If validated then continue with change of state 
			g_crCallResult = xController.checkPinCode(sPincode1, sPincode2);
			if (g_crCallResult.getResult() == g_crCallResult.RESULT_OK)
			{
				/* change state to close */
				g_crCallResult = xController.close();
				LogHelper.log(
					LogHelper.INFO,
					"[CloseCommand.exeute] system is closed, starting backup ");
				/* Call script to backup database to removable medium */
				try
				{
					String sScriptPath =
						TechnicalProps.getProperty(
							TechnicalProps.BACKUP_SCRIPT_FS);
					if (sScriptPath != null)
					{
						Process xProcess =
							Runtime.getRuntime().exec(sScriptPath);
						int iProcessRes = xProcess.waitFor();
						if (iProcessRes != 0)
						{
							// process has terminated or subprocess has terminated
							bBackupFailed = true;
							LogHelper.log(
								LogHelper.INFO,
								"[CloseCommand.exeute] backup to filesystem FAILED...");
							// Let the voorzitter know that the export to filesystem has failed
							sMessage =
								com
									.logica
									.eplatform
									.error
									.ErrorMessageFactory
									.getErrorMessageFactory()
									.getErrorMessage(
										ErrorConstants.CREATE_FS_BACKUP_ERROR,
										null);
							KOALogHelper.audit(
								KOALogHelper.INFO,
								AuditEventListener.STATE_CHANGE,
								"CloseElection",
								g_sUser,
								sMessage);
							KOALogHelper.log(
								KOALogHelper.ERROR,
								"Error executing script for backup to fs (close state) code = "
									+ iProcessRes);
							g_crCallResult.setBackupResult(sMessage);
						}
						else
						{
							bBackupFailed = false;
							LogHelper.log(
								LogHelper.INFO,
								"[CloseCommand.exeute] backup to filesystem OK...");
							// Let the voorzitter know that the export to filesystem has succeeded
							sMessage =
								com
									.logica
									.eplatform
									.error
									.ErrorMessageFactory
									.getErrorMessageFactory()
									.getErrorMessage(
										ErrorConstants.CREATE_FS_BACKUP_OK,
										null);
							KOALogHelper.audit(
								KOALogHelper.INFO,
								AuditEventListener.STATE_CHANGE,
								"CloseElection",
								g_sUser,
								sMessage);
							g_crCallResult.setBackupResult(sMessage);
						}
					}
					// If backup to filesystem succeeded then write backup to tape as a background process.
					if (!bBackupFailed)
					{
						LogHelper.log(
							LogHelper.INFO,
							"[CloseCommand.exeute] Start writing to tape...");
						sScriptPath =
							TechnicalProps.getProperty(
								TechnicalProps.BACKUP_SCRIPT_TAPE);
						// Execute backup to tape. This should run in the background.
						if (sScriptPath != null)
						{
							Process xProcess =
								Runtime.getRuntime().exec(sScriptPath);
						}
						String sTapeBackupMessage =
							com
								.logica
								.eplatform
								.error
								.ErrorMessageFactory
								.getErrorMessageFactory()
								.getErrorMessage(
									ErrorConstants.CHECK_TAPE_BACKUP,
									null);
						sMessage = sMessage + " " + sTapeBackupMessage;
						KOALogHelper.audit(
							KOALogHelper.INFO,
							AuditEventListener.STATE_CHANGE,
							"CloseElection",
							g_sUser,
							sMessage);
						g_crCallResult.setBackupResult(sMessage);
					}
				}
				catch (java.lang.InterruptedException xInterruptedExc)
				{
					bBackupFailed = true;
					KOALogHelper.logErrorCode(
						"CloseCommand.execute",
						ErrorConstants.UNABLE_TO_START_BACKUP_SCRIPT,
						null,
						xInterruptedExc);
				}
				catch (java.io.IOException xioExc)
				{
					bBackupFailed = true;
					String[] params = { "backupscript" };
					KOALogHelper.logErrorCode(
						"CloseCommand.execute",
						ErrorConstants.ERR_IO,
						params,
						xioExc);
				}
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"CloseCommand.execute",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(ErrorConstants.COMMAND_CLOSE_EXEC, ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"CloseCommand.execute",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.COMMAND_CLOSE_EXEC, re);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"CloseCommand.execute",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.COMMAND_CLOSE_EXEC, ce);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError("CloseCommand.execute", "KOAException", koae);
			throw koae;
		}
		finally
		{
			if (bBackupFailed)
			{
				if (sMessage == null)
				{
					// I/O Error while executing backup script for exporting to filesystem or
					// InterruptedException while waiting for process to be finished. These two errors result in the
					// same result: "backup in general has failed"
					try
					{
						sMessage =
							com
								.logica
								.eplatform
								.error
								.ErrorMessageFactory
								.getErrorMessageFactory()
								.getErrorMessage(
									ErrorConstants.CREATE_BACKUP_ERROR,
									null);
						KOALogHelper.audit(
							KOALogHelper.ERROR,
							AuditEventListener.STATE_CHANGE,
							"CloseElection",
							g_sUser,
							sMessage);
						g_crCallResult.setBackupResult(sMessage);
						LogHelper.log(
							LogHelper.ERROR,
							"[CloseCommand.exeute] Error occured with result that back up is not created...");
					}
					catch (java.io.IOException ioe)
					{
						String[] params = { "Error message factory" };
						KOALogHelper.logErrorCode(
							"CloseCommand.execute",
							ErrorConstants.ERR_IO,
							params,
							ioe);
					}
				}
				else
				{
					// Backup failed through process termination or subprocess termination
					KOALogHelper.audit(
						KOALogHelper.ERROR,
						AuditEventListener.STATE_CHANGE,
						"CloseElection",
						g_sUser,
						sMessage);
					LogHelper.log(
						LogHelper.ERROR,
						"[CloseCommand.exeute] Error occured with result that back up is not created...");
				}
			}
		}
	}
	/**
	 * Initialises the command. Here the parameters are
	 * extracted from the request.
	 *
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * 
	 * @throws EPlatformException	necessary to fullfill abstract method signature
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[CloseCommand.init] init");
		/* get the pincodes */
		sPincode1 = request.getParameter("pincode1");
		sPincode2 = request.getParameter("pincode2");
		/* get the user */
		g_sUser = request.getUserPrincipal().getName();
	}
}