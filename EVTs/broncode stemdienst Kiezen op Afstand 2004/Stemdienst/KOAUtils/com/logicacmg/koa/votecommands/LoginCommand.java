/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.LoginCommand.java
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
  *  1.0		17-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.votecommands;
import com.logica.eplatform.command.AbstractTargetableCommand;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.votecommands.CommandConstants;
/**
 * Only function of this command is to logon somebody.
 * Only use this command if you want to explicitly log somebody on to the 
 * system without performing a specific task.
 * 
 * @author: KuijerM
 */
public class LoginCommand
	extends AbstractTargetableCommand
	implements HttpCommand
{
	private final static String NEXT_JSP = "/WEB-INF/jsp/ChooseCandidate.jsp";
	/**
	 * The execute method on the Login command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	necessary to fullfill abstract method signature
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		KOALogHelper.log(KOALogHelper.INFO, "[LoginCommand] execute");
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[LoginCommand] leaving execute()");
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
		return NEXT_JSP;
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
		KOALogHelper.log(KOALogHelper.TRACE, "[LoginCommand] init");
	}
	/**
	 * Update the current session.
	 * 
	 * @param HttpSession	session the session to update
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[LoginCommand] entering updateSession");
		/* reset the kandidaat code in the session */
		session.removeAttribute(CommandConstants.KANDIDAATCODE);
	}
}