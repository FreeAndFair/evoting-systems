/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.ticket.KOATicketResponse.java
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
  *  0.1		07-04-2003	Xui		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.ticket;
import com.logica.eplatform.ticket.Ticket;
import com.logicacmg.koa.dataobjects.StemTransactie;
/**
 * KoaTicketResponse wraps the ticket object and the stemtransactie object
 */
public class KOATicketResponse
{
	private Ticket xTicket = null;
	private StemTransactie xStemTransactie = null;
	private String sMessage = null;
	private int iTimeToUnlock = 0;
	/**
	 * Gets the ticket
	 * 
	 * @return Ticket
	 */
	public Ticket getTicket()
	{
		return xTicket;
	}
	/**
	 * Sets the ticket
	 * 
	 * @param ticket The ticket to set
	 */
	public void setTicket(Ticket ticket)
	{
		xTicket = ticket;
	}
	/**
	 * Gets the stemTransactie
	 * 
	 * @return StemTransactie
	 */
	public StemTransactie getStemTransactie()
	{
		return xStemTransactie;
	}
	/**
	 * Sets the stemTransactie
	 * 
	 * @param stemTransactie The stemTransactie to set
	 */
	public void setStemTransactie(StemTransactie stemTransactie)
	{
		xStemTransactie = stemTransactie;
	}
	/**
	 * Gets the message
	 * 
	 * @return String
	 */
	public String getMessage()
	{
		return sMessage;
	}
	/**
	 * Sets the message
	 * 
	 * @param message The message to set
	 */
	public void setMessage(String message)
	{
		sMessage = message;
	}
	/**
	 * Gets the timeToUnlock
	 * 
	 * @return int
	 */
	public int getTimeToUnlock()
	{
		return iTimeToUnlock;
	}
	/**
	 * Sets the timeToUnlock
	 * 
	 * @param timeToUnlock The timeToUnlock to set
	 */
	public void setTimeToUnlock(int timeToUnlock)
	{
		iTimeToUnlock = timeToUnlock;
	}
}