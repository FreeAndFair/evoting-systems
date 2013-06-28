/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.FetchDataCommand.java
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
  *  1.0		15-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.voorzitter.command;
import java.rmi.RemoteException;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
import com.logicacmg.koa.voorzitter.command.CommandConstants;
/**
 * FetchDataCommand.
 * Use this command to fetch data from the KOA system.
 * 
 * @author: KuijerM
 * 
 */
public class FetchDataCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand
{
	private java.lang.String RESULT_JSP = "fetchdata.jsp";
	private java.lang.String g_sCurrentState;
	/**
	 * The execute method on the FetchData command.
	 * This method is executed in the ejb command target.
	 *
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of the Controller can not be created.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.log(LogHelper.INFO, "[FetchDataCommand.execute] start");
		try
		{
			ControllerHome xControllerHome =
				ObjectCache.getInstance().getControllerHome();
			/* create remote instance from the home interface */
			Controller xController = xControllerHome.create();
			/* get the current state */
			g_sCurrentState = xController.getCurrentState();
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"FetchDataCommand.execute",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.COMMAND_GETSTATE_EXEC, ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"FetchDataCommand.execute",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.COMMAND_GETSTATE_EXEC, re);
		}
	}
	/**
	 * Return the JSP to display errors.
	 * 
	 * @return String The error JSP
	 */
	public String getErrorJSP()
	{
		return CommandConstants.DEFAULT_ERROR_JSP;
	}
	/**
	 * Return the JSP page to display the result.
	 *
	 * @return String The result JSP
	 */
	public String getResultJSP()
	{
		return RESULT_JSP;
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
		LogHelper.trace(LogHelper.TRACE, "[FetchDataCommand] init");
	}
	/**
	 * Update the current session.
	 * 
	 * @param HttpSession	The session to be updated
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
	/**
	 * Return the state which was retrieved in the execute() method.
	 *
	 * @return String	The current state
	 */
	public String getCurrentState()
	{
		return g_sCurrentState;
	}
}