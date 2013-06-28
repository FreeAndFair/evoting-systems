/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.ticket.KOATicket.java
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
package com.logicacmg.koa.ticket;
/**
 * The authorization ticket for the KOA application based on username and the
 * roles.
 * 
 * @author: KuijerM
 */
public class KOATicket extends com.logica.eplatform.ticket.Ticket
{
	/**
		 * The role that is used for the voter
	 * 
	 */
	public static final String STEMGERECHTIGDE_ROLE = "stemgerechtigde";
	/**
	 * The role that is used for the chairman
	 */
	public static final String VOORZITTER_ROLE = "voorzitter";
	/**
	 * The role that is used for the data manager
	 */
	public static final String DATABEHEER_ROLE = "databeheer";
	/**
	 * The constructor for the KOATicket
	 * @param userID The user id to create the ticket for
	 * @param roles the roles this user obtains
	 * @param expiry The date the ticket is expired
	 */
	protected KOATicket(
		String userID,
		java.util.Vector roles,
		java.util.Date expiry)
	{
		super(userID, roles, expiry);
	}
}