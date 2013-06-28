/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.ticket.PrincipalTicketRequest.java
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
  *  1.0		23-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.ticket;
import com.logica.eplatform.ticket.TicketRequest;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * PrincipalTicketRequest is used to read the 
 * user from the principal.
 * 
 * The principal is filled through the Websphere authentication
 * mechanism.
 * 
 * @author KuijerM
 */
public class PrincipalTicketRequest extends TicketRequest
{
	/* the request to use */
	private HttpServletRequest g_xRequest = null;
	/**
	 * Constructor for the principal ticket request
	 * 
	 * @param xRequest The request to use for reading of the username
	 */
	public PrincipalTicketRequest(HttpServletRequest xRequest)
	{
		this.g_xRequest = xRequest;
	}
	/**
	 * Get the username that is entered through the
	 * Webpshere authentication mechanism.
	 * 
	 * @return String	the username of the logged in person
	 */
	public String getUserName()
	{
		try
		{
			/* try to get the principal from the request and get the username */
			String sUser = g_xRequest.getUserPrincipal().getName();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[PrincipalTicketRequest.getUserName] Found user "
					+ sUser
					+ ", returning username");
			return sUser;
		}
		catch (NullPointerException npe)
		{
			/* if we get a null pointer, it means no username is present */
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[PrincipalTicketRequest.getUserName] Could not find username for a chairman, user is not authorized");
			return null;
		}
	}
	/**
	 * Check if the user that is logged in, has the appropriate roles
	 * 
	 * @param sRole The role to check for
	 * 
	 * @return boolean true if the user has the role, false otherwise.
	 * 
	 */
	public boolean isUerInRole(String sRole)
	{
		/* check if the user that logged in via Websphere authentication, 
		   as the appropriate role */
		return g_xRequest.isUserInRole(sRole);
	}
}