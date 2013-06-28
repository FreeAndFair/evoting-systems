/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.command.SelectUploadCommand.java
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
  *  0.1		04-07-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.command;
import java.rmi.RemoteException;
import java.util.Hashtable;
import java.util.Map;
import java.util.TreeMap;
import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Select upload command is used to select the right type of upload
 * page and gets the status of the system to make sure the 
 * system is in the right state to upload the file.
 * Otherwise a message is shown.
 * 
 * @author: KuijerM
 */
public class SelectUploadCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand
{
	public static final String ACTION = "action";
	public final static String VOTER_REMOVE = "verwijder_kiezers";
	public final static String VOTER_REPLACE = "vervang_kiezers";
	public final static String VOTER_APPEND = "toevoegen_kiezers";
	public final static String CANDIDATES_REPLACE = "vervang_kandidaten";
	private java.lang.String RESULT_JSP;
	private java.lang.String g_sAction = null;
	private java.lang.String g_sMessage = "";
	private static Map xStateMapping;
	// this code wil be executed at class loading
	static {
		xStateMapping = new TreeMap();
		xStateMapping.put(
			CANDIDATES_REPLACE,
			new String[] { SystemState.PREPARE });
		xStateMapping.put(
			VOTER_REMOVE,
			new String[] { SystemState.OPEN, SystemState.PREPARE });
		xStateMapping.put(
			VOTER_APPEND,
			new String[] { SystemState.OPEN, SystemState.PREPARE });
		xStateMapping.put(VOTER_REPLACE, new String[] { SystemState.PREPARE });
	}
	/**
	 * The execute method on the Login command.
	 * This method is executed in the ejb command target.
	 * For the LoginCommand the execute method doesn't do anything.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.log(LogHelper.INFO, "[LoginCommand] execute");
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
		try
		{
			InitialContext ic = new InitialContext(htProps);
			Object obj =
				ic.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			ControllerHome home =
				(ControllerHome) javax.rmi.PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			Controller controller = home.create();
			String sCurrentState = controller.getCurrentState();
			String[] saState = (String[]) xStateMapping.get(g_sAction);
			KOALogHelper.log(
				LogHelper.INFO,
				"[Upload] Upload state = " + sCurrentState);
			// check the state
			boolean check = false;
			String sValidStates = "";
			if (saState != null)
			{
				for (int i = 0; i < saState.length; i++)
				{
					if (!sValidStates.equals(""))
					{
						sValidStates += ", ";
					}
					sValidStates
						+= SystemState.getDutchTranslationForState(saState[i]);
					if ((saState != null)
						&& (saState[i].equals(sCurrentState)))
					{
						check = true;
					}
				}
			}
			if (!check)
			{
				g_sMessage =
					"Deze actie is niet toegestaan tijdens de systeemstatus: "
						+ SystemState.getDutchTranslationForState(sCurrentState)
						+ ". "
						+ "Deze actie is alleen toegestaan tijdens de systeemstatus: "
						+ sValidStates;
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[SelectUploadCommand]",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[SelectUploadCommand]",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				re);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[SelectUploadCommand]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ce);
		}
	}
	/**
	 * Return the JSP to display errors.
	 * @return String The error JSP
	 */
	public String getErrorJSP()
	{
		return CommandConstants.DEFAULT_ERROR_JSP;
	}
	/**
	 * Return the JSP page to display the result.
	 * @return String The result JSP
	 */
	public String getResultJSP()
	{
		return RESULT_JSP;
	}
	public String getMessage()
	{
		return g_sMessage;
	}
	/**
	 * Initialises the command. In the init the parameters can be
	 * extracted from the request.
	 * @param request The current request
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[LoginCommand] init");
		/*  */
		g_sAction = request.getParameter(ACTION);
		if (g_sAction == null)
		{
			RESULT_JSP = "index.jsp";
		}
		else if (g_sAction.equals(VOTER_APPEND))
		{
			RESULT_JSP = "update.jsp";
		}
		else if (g_sAction.equals(VOTER_REMOVE))
		{
			RESULT_JSP = "verwijder.jsp";
		}
		else if (g_sAction.equals(VOTER_REPLACE))
		{
			RESULT_JSP = "vervang.jsp";
		}
		else if (g_sAction.equals(CANDIDATES_REPLACE))
		{
			RESULT_JSP = "kieslijst.jsp";
		}
	}
	/**
	 * Update the current session.
	 * @param session the session to update
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
}