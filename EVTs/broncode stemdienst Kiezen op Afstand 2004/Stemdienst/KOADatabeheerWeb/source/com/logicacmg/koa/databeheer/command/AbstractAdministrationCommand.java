/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.voorzitter.command.AbstractAdministrationCommand.java
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
  *  0.1		28-04-2003	MKu	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.command;
import com.logica.eplatform.command.AbstractTargetableCommand;
import com.logica.eplatform.command.CommandException;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.dataobjects.AbstractAdministrationObject;
/**
 * Abstract command for all the administration commands.
 * 
 * @author KuijerM
 * 
 */
public abstract class AbstractAdministrationCommand
	extends AbstractTargetableCommand
	implements HttpCommand
{
	// which report
	protected String selectedKey = null;
	protected int pageNo = 1;
	// Data object
	protected AbstractAdministrationObject overview = null;
	/**
	 * initialize the command
	 * Read the key and the page number from the request
	 * Selected key has got parameter id 'id'
	 * The page number has got parameter id 'page'
	 * 
	 * @param request javax.servlet.http.HttpServletRequest
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		// get selkectedKey
		selectedKey = request.getParameter("id");
		String s = request.getParameter("page");
		if (s != null)
			pageNo = Integer.parseInt(s);
	}
	/**
	 * Abstract method that must be implemented by all deriving commands.
	 */
	public abstract void execute() throws CommandException, EPlatformException;
	/**
	 * Returns the error jsp specified.
	 * 
	 * @return java.lang.String The error JSP
	 * 
	 */
	public String getErrorJSP()
	
	{
		return CommandConstants.DEFAULT_ERROR_JSP;
	}
	/**
	 * Get the result jsp for this command
	 * 
	 * @return java.lang.String
	 * 
	 */
	public String getResultJSP()
	{
		return (selectedKey != null)
			? overview.getDetailJSP()
			: overview.getOverviewJSP();
	}
	/**
	 * Update the session and set the administration object in the session
	 * 
	 * @param session javax.servlet.http.HttpSession
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
		if (overview != null)
			session.setAttribute(
				CommandConstants.ADMIN_OBJECT_IN_SESSION,
				overview);
	}
	/**
	 * Get the selected key that is specified in the request parameters
	 * 
	 * @return String the selected key
	 * 
	 */
	public String getSelectedKey()
	{
		return selectedKey;
	}
	/**
	 * Get the page number
	 * 
	 * @return int the page number
	 * 
	 */
	public int getPageNo()
	{
		return pageNo;
	}
	/**
	 * Gets the overview object
	 * 
	 * @return Object the overview object
	 * 
	 */
	public Object getOverview()
	{
		return overview;
	}
	/**
	 * Helper method to determine if the string contains
	 * SQL characters.
	 * 
	 * @return boolean indicating if there are SQL characters
	 * 
	 */
	private boolean containsSQLChars(String string)
	{
		boolean contains = false;
		if (string.indexOf("'") > -1)
			contains = true;
		else if (string.indexOf("\"") > -1)
			contains = true;
		else if (string.indexOf("(") > -1)
			contains = true;
		else if (string.indexOf(")") > -1)
			contains = true;
		else if (string.indexOf("@") > -1)
			contains = true;
		return contains;
	}
	/**
	 * Helper method to check if the date is valid.
	 * The date should be in the format 'yyyy-MM-dd'
	 * 
	 * @param date the Date to check
	 * 
	 * @return boolean indicating if it is a valid date (true) or no valid date (false)
	 * 
	 */
	private boolean isValidDate(String date)
	{
		char[] chars = date.toCharArray();
		if (chars.length != 10)
			return false;
		return Character.isDigit(chars[0])
			&& Character.isDigit(chars[1])
			&& Character.isDigit(chars[2])
			&& Character.isDigit(chars[3])
			&& chars[4] == '-'
			&& Character.isDigit(chars[5])
			&& Character.isDigit(chars[6])
			&& chars[7] == '-'
			&& Character.isDigit(chars[8])
			&& Character.isDigit(chars[9]);
	}
}