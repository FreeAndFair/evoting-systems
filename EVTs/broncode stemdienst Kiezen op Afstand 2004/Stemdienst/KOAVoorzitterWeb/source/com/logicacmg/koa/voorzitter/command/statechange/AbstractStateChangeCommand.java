/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.AbstractStateChangeCommand.java
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
import java.util.Iterator;
import java.util.List;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.dataobjects.CallResult;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.voorzitter.command.CommandConstants;
/**
 * Abstract class that is used for all commands
 * that do a state change.
 * 
 * @author: KuijerM
 */
public abstract class AbstractStateChangeCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand
{
	protected java.lang.String RESULT_JSP = "statechange_result.jsp";
	protected CallResult g_crCallResult = null;
	protected String sPincode1 = null;
	protected String sPincode2 = null;
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
	 * Return the call result. The call result is set
	 * by a subclass.
	 *
	 * @return CallResult
	 */
	public CallResult getCallResult()
	{
		return g_crCallResult;
	}
	/**
	 * Return the state which was retrieved and stored in a call result by a subclass.
	 *
	 * @return String	The current state
	 */
	public String getCurrentState()
	{
		String sCurrentState = SystemState.UNKNOWN;
		if (g_crCallResult != null && g_crCallResult.getCurrentState() != null)
		{
			sCurrentState = g_crCallResult.getCurrentState();
		}
		return sCurrentState;
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
	 * Update the current session.
	 * 
	 * @param HttpSession	The session to be updated
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
	/**
	 * This method returns the upload file from the HttpServletRequest
	 * 
	 * @param  HttpServletRequest 	the HttpServletRequest whit the upload file
	 * @return Iterator 			a list with all the items (FileItem) from xReq
	 */
	protected Iterator getFileItem(HttpServletRequest xReq) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[InitializeCommand.getFileItem] getting files from request");
		try
		{
			FileUpload xFu = new FileUpload();
			// maximum size before a FileUploadException will be thrown
			xFu.setSizeMax(4096);
			// maximum size that will be stored in memory
			xFu.setSizeThreshold(4096);
			List xFileItems = xFu.parseRequest(xReq);
			return xFileItems.iterator();
		}
		catch (FileUploadException fue)
		{
			KOALogHelper.logError(
				"AbstractStateChangeCommand.getFileItem",
				"Error getting the fileitems from the request",
				fue);
			throw new KOAException(ErrorConstants.COMMAND_GET_FILEITEM, fue);
		}
	}
}