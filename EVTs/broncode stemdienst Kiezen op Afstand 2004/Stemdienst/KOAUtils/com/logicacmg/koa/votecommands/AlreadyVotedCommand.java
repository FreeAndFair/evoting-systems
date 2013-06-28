/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.AlreadyVotedCommand.java
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
  *  0.1		20-05-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.votecommands;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.dataobjects.Kiezer;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.votecommands.CommandConstants;
/**
 * Command to execute when somebody already voted.
 * 
 * @author GroenevA
 */
public class AlreadyVotedCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand
{
	private final static String NEXT_JSP = "/WEB-INF/jsp/alreadyvoted.jsp";
	private String sErrorMessage = null;
	private Kiezer g_xKiezer = null;
	/**
	 * The execute method on the AlreadyVotedCommand
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	necessary to fullfill abstract method signature
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		KOALogHelper.log(KOALogHelper.INFO, "[AlreadyVotedCommand] execute");
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[AlreadyVotedCommand] leaving execute()");
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
		KOALogHelper.log(KOALogHelper.TRACE, "[AlreadyVotedCommand] init");
		if (request.getAttribute(CommandConstants.KIEZER_OBJECT) != null)
		{
			g_xKiezer =
				(Kiezer) request.getAttribute(CommandConstants.KIEZER_OBJECT);
		}
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
			"[AlreadyVotedCommand] entering updateSession");
	}
	/**
	 * Returns a Kiezer dataobject
	 * 
	 * @return Kiezer	The kiezer which was read from the request in the init() method
	 */
	public Kiezer getKiezer()
	{
		return g_xKiezer;
	}
	/**
	 * Translates a technical key to a user friendly string
	 * 
	 * @param String	The key to be translated
	 * 
	 * @return String	The trasnlation when key is found else a string with size = 0;
	 */
	public String translateTechnicalKey(String sKey)
	{
		if (sKey == null)
		{
			return "";
		}
		try
		{
			if (sKey.equals(ComponentType.WEB))
			{
				return FunctionalProps.getProperty(FunctionalProps.SOURCE_WEB);
			}
			if (sKey.equals(ComponentType.TEL))
			{
				return FunctionalProps.getProperty(FunctionalProps.SOURCE_TEL);
			}
		}
		catch (KOAException xKOAExc)
		{
			KOALogHelper.logError(
				"[AlreadyVotedCommand] ",
				xKOAExc.getMessage(),
				xKOAExc);
		}
		return "";
	}
}