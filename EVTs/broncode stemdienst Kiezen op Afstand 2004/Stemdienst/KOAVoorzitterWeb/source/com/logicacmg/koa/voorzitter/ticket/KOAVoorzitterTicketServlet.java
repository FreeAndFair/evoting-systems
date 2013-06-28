/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.ticket.KOATicketServlet.java
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
package com.logicacmg.koa.voorzitter.ticket;
import java.io.IOException;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.ticket.Ticket;
import com.logica.eplatform.ticket.TicketConstants;
import com.logica.eplatform.ticket.TicketFactory;
import com.logica.eplatform.ticket.TicketRequest;
import com.logicacmg.koa.ticket.KOAVoorzitterTicketFactory;
import com.logicacmg.koa.ticket.PrincipalTicketRequest;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Servlet to handle the management of tickets for the web channel.
 * 
 * @author: KuijerM
 */
public class KOAVoorzitterTicketServlet
	extends com.logica.eplatform.servlet.UtilServlet
{
	protected TicketFactory factory;
	/**
	 * init the ticket factory
		*/
	public void init()
	{
		/* get the singleton implementation of the ticket factory */
		factory = KOAVoorzitterTicketFactory.getTicketFactory();
		super.init();
	}
	/**
	 * Handle the GET request
	 * 
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * @param HttpServletResponse	Object that encapsulates the response from the servlet
	 * 
	 * @throws ServletException thrown by performTask(request, response)
	 * @throws IOException		thrown by performTask(request, response)
	 */
	public void doGet(HttpServletRequest request, HttpServletResponse response)
		throws ServletException, IOException
	{
		performTask(request, response);
	}
	/**
	 * Handle the POST request
	 * 
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * @param HttpServletResponse	Object that encapsulates the response from the servlet
	 * 
	 * @throws ServletException thrown by performTask(request, response)
	 * @throws IOException		thrown by performTask(request, response)
	 */
	public void doPost(
		HttpServletRequest request,
		HttpServletResponse response)
		throws ServletException, IOException
	{
		performTask(request, response);
	}
	/**
	 * Handle the GET or POST request
	 * 
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * @param HttpServletResponse	Object that encapsulates the response from the servlet
	 * 
	 * @throws ServletException thrown by super.redirect
	 * @throws IOException		thrown by super.redirect
	 */
	public void performTask(
		HttpServletRequest request,
		HttpServletResponse response)
		throws ServletException, IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAVoorzitterTicketServlet.performTask] try to get ticket for chairman");
		TicketRequest tr = new PrincipalTicketRequest(request);
		Ticket ticket = null;
		try
		{
			ticket = factory.getTicket(tr);
		}
		catch (EPlatformException ep)
		{
			KOALogHelper.logError(
				"KOAVoorzitterTicketServlet.performTask",
				"Could Eplatform exception during get ticket",
				ep);
			redirect(
				request,
				response,
				props.getProperty(
					"com.logica.eplatform.error.DefaultErrorPage"));
			return;
		}
		if (ticket == null)
		{
			KOALogHelper.logError(
				"KOAVoorzitterTicketServlet.performTask",
				"No ticket found",
				null);
			redirect(
				request,
				response,
				props.getProperty(
					"com.logica.eplatform.error.DefaultErrorPage"));
			return;
		}
		request.getSession(true).setAttribute(
			TicketConstants.TICKET_IN_SESSION,
			ticket);
		redirect(
			request,
			response,
			(String) request.getSession(true).getAttribute(
				TicketConstants.REQUESTED_RESOURCE_IN_SESSION));
	}
}