/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.command.LoginCommand.java
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
  *  1.0		11-04-2003	MRo		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.command;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.databeheer.command.CommandConstants;
/**
 * LoginCommand. Only function of this command is to logon somebody.
 * Only use this command if you want to explicitly log somebody on to the 
 * system without performing a specific task.
 * Creation date: (07-04-2003 14:07:30)
 * @author: KuijerM
 */
public class LoginCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand
{
	private java.lang.String RESULT_JSP;
	private boolean logout = false;
	/**
	 * The execute method on the Login command.
	 * This method is executed in the ejb command target.
	 * For the LoginCommand the execute method doesn't do anything.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.log(LogHelper.INFO, "[LoginCommand] execute");
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
	 * Initialises the command. In the init the parameters can be
	 * extracted from the request.
	 * 
	 * @param request The current request
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[LoginCommand] init");
		/*  */
		RESULT_JSP = request.getParameter("page");
		if (RESULT_JSP == null)
			RESULT_JSP = "index.jsp";
	}
	/**
	 * Update the current session.
	 * 
	 * @param session the session to update
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
}
