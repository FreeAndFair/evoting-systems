/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.CommandConstants.java
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
  *  1.0		07-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.voorzitter.command;
/**
 * Class containing all the constants for the commands.
 * 
 * @author: KuijerM
 */
public class CommandConstants
{
	/* context root for the web environment */
	final static java.lang.String CONTEXT_PATH = "/KOAVoorzitterWeb";
	/* page used as default error JSP */
	public final static java.lang.String DEFAULT_ERROR_JSP = "/error.jsp";
	/* the key used to store the requested command in the session */
	public final static java.lang.String COMMAND_IN_REQUEST_KEY = "COMMAND";
	/* the key used to store the selection of the proces verbaal select in the session */
	public final static java.lang.String SELECT_PROCES_VERBAAL_SELECTION =
		"selection";
}