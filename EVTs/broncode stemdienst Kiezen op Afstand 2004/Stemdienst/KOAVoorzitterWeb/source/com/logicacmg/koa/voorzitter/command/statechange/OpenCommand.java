/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.OpenCommand.java
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
  *  1.0		01-05-2003	MKu			First implementation
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
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.voorzitter.command.statechange.AbstractStateChangeCommand;
/**
 * Change state to open.
 * 
 * @author KuijerM
 * 
 */
public class OpenCommand extends AbstractStateChangeCommand
{
	/**
	 * The execute method on the Open command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of the Controller can not be created.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.log(LogHelper.INFO, "[OpenCommand.exeute] execute ");
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
				/* change state to open */
				g_crCallResult = xController.open();
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"OpenCommand.execute",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(ErrorConstants.COMMAND_OPEN_EXEC, ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"OpenCommand.execute",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.COMMAND_OPEN_EXEC, re);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"OpenCommand.execute",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.COMMAND_OPEN_EXEC, ce);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError("OpenCommand.execute", "KOAException", koae);
			throw koae;
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
		LogHelper.trace(LogHelper.TRACE, "[OpenCommand.init] init");
		/* get the pincodes */
		sPincode1 = request.getParameter("pincode1");
		sPincode2 = request.getParameter("pincode2");
	}
}
