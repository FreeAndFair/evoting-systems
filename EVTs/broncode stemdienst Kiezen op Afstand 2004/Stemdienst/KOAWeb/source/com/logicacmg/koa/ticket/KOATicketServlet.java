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
package com.logicacmg.koa.ticket;
import java.io.IOException;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.error.ErrorMessageFactory;
import com.logica.eplatform.servlet.UtilServlet;
import com.logica.eplatform.ticket.Ticket;
import com.logica.eplatform.ticket.TicketConstants;
import com.logica.eplatform.ticket.TicketRequest;
import com.logica.eplatform.ticket.UserPwdTicketRequest;
import com.logica.eplatform.util.SystemProperties;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.controller.client.ClientManager;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.ticket.KOATicketFactory;
import com.logicacmg.koa.ticket.KOATicketResponse;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.votecommands.CommandConstants;
/**
 * Servlet to handle the management of tickets for the web channel.
 * @author: KuijerM
 */
public class KOATicketServlet extends UtilServlet
{
	protected KOATicketFactory factory = null;
	/**
	 * init the ticket factory
	 */
	public void init()
	{
		/* get the singleton implementation of the ticket factory */
		factory = (KOATicketFactory) KOATicketFactory.getTicketFactory();
		super.init();
	}
	/**
	 * Redirects to the login page
	 * 
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * @param HttpServletResponse	Object that encapsulates the response from the servlet
	 * 
	 * @throws ServletException thrown by super.redirect
	 * @throws IOException		thrown by super.redirect
	 */
	public final void doGet(
		HttpServletRequest request,
		HttpServletResponse response)
		throws ServletException, IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[UserPwdTicketServlet] Get Request");
		redirect(
			request,
			response,
			props.getProperty("com.logica.eplatform.ticket.UserPwdLoginPage"));
	}
	/**
	 *	Checks if the login data is correct
	 *  If the data is not correct, it redirects to the default error page and sets the error message in the session
	 * 
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * @param HttpServletResponse	Object that encapsulates the response from the servlet
	 * 
	 * @throws ServletException thrown by super.redirect
	 * @throws IOException		thrown by super.redirect
	 */
	public final void doPost(
		HttpServletRequest request,
		HttpServletResponse response)
		throws ServletException, IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[UserPwdTicketServlet] post request");
		// Ask for Ticket from Factory
		TicketRequest tr =
			new UserPwdTicketRequest(
				request.getParameter("USER"),
				request.getParameter("PWD"));
		KOATicketResponse xTicketResponse = null;
		Ticket ticket = null;
		StemTransactie xStemTransactie = null;
		try
		{
			/* get the ticketresponse from the factory */
			xTicketResponse =
				factory.getTicketResponse(tr, ComponentType.WEB, true);
			if (xTicketResponse != null)
			{
				/* get the ticket */
				ticket = xTicketResponse.getTicket();
				xStemTransactie = xTicketResponse.getStemTransactie();
				//collect counters
				if (xStemTransactie.VoteStatus
					== StemTransactie.ELECTION_NOT_YET_OPEN
					|| xStemTransactie.VoteStatus
						== StemTransactie.ELECTION_CLOSED
					|| xStemTransactie.VoteStatus
						== StemTransactie.ELECTION_BLOCKED
					|| xStemTransactie.VoteStatus
						== StemTransactie.ELECTION_SUSPENDED)
				{
					ClientManager.updateCounter(
						ComponentType.WEB,
						CounterKeys.OPROEPEN_BUITEN_BEDRIJF);
				}
				else if (
					xStemTransactie.VoteStatus == StemTransactie.OK
						|| xStemTransactie.VoteStatus
							== StemTransactie.ACCOUNT_LOCKED
						|| xStemTransactie.VoteStatus
							== StemTransactie.INVALID_CREDENTIALS
						|| xStemTransactie.VoteStatus
							== StemTransactie.ALREADY_VOTED)
				{
					ClientManager.updateCounter(
						ComponentType.WEB,
						CounterKeys.OPROEPEN_BEDRIJF);
				}
				if (xStemTransactie.VoteStatus == StemTransactie.OK
					|| xStemTransactie.VoteStatus == StemTransactie.ALREADY_VOTED)
				{
					ClientManager.updateCounter(
						ComponentType.WEB,
						CounterKeys.VERIFICATIE_GELUKT);
				}
				else if (
					xStemTransactie.VoteStatus
						== StemTransactie.ACCOUNT_LOCKED)
				{
					/* update counter if account locked */
					ClientManager.updateCounter(
						ComponentType.WEB,
						CounterKeys.VERIFICATIE_MISLUKT);
					request.setAttribute(
						CommandConstants.KIEZER_LOGIN_FAILED,
						new Boolean(true));
				}
				HttpSession xSession = request.getSession(true);
				Integer iNumberOfAttempts =
					(Integer) xSession.getAttribute(
						CommandConstants.LOGIN_ATTEMPTS);
				int iAttemptsCounter = 0;
				if (iNumberOfAttempts != null)
				{
					iAttemptsCounter = iNumberOfAttempts.intValue();
				}
				// Increase login attempts	
				iAttemptsCounter++;
				iNumberOfAttempts = new Integer(iAttemptsCounter);
				xSession.setAttribute(
					CommandConstants.LOGIN_ATTEMPTS,
					iNumberOfAttempts);
				/* reset the kandidaat code in the session */
				xSession.removeAttribute(CommandConstants.KANDIDAATCODE);
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[UserPwdTicketServlet] xStemTransactie.VoteStatus = "
						+ xStemTransactie.VoteStatus);
				//if kiezer has already voted then redirect
				if (xStemTransactie.VoteStatus == StemTransactie.ALREADY_VOTED)
				{
					request.setAttribute(
						CommandConstants.KIEZER_OBJECT,
						xStemTransactie.kiezer);
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[UserPwdTicketServlet] saving ticket in session");
					request.getSession(true).setAttribute(
						TicketConstants.TICKET_IN_SESSION,
						ticket);
					redirect(
						request,
						response,
						CommandConstants.ALREADY_VOTED_ALIAS);
					return;
				}
				ErrorMessageFactory emf =
					ErrorMessageFactory.getErrorMessageFactory();
				int iMaxAttempts =
					FunctionalProps.getIntProperty(
						FunctionalProps.LOGIN_ATTEMPTS_COUNT);
				// if stemcode does not consist of digits then redirect.
				if (xStemTransactie.VoteStatus
					== StemTransactie.NON_NUMERIC_CODE)
				{
					if (iNumberOfAttempts.intValue() < iMaxAttempts)
					{
						request.setAttribute(
							CommandConstants.INLOG_ERROR,
							emf.getErrorMessage(
								ErrorConstants.VERIFY_STEM_CODE_NUMERIC_ERR,
								null));
						redirect(
							request,
							response,
							CommandConstants.IDENTIFICATION_JSP);
						return;
					}
					else
					{
						ClientManager.updateCounter(
							ComponentType.WEB,
							CounterKeys.VERIFICATIE_MISLUKT);
						request.setAttribute(
							CommandConstants.ERROR_IN_REQUEST_KEY,
							emf.getErrorMessage(
								ErrorConstants.MAX_ATTEMPTS_EXCEEDED,
								null));
						redirect(
							request,
							response,
							CommandConstants.DEFAULT_ERROR_JSP);
						return;
					}
				}
				// if stemcode is not 9 digits long then redirect.
				if (xStemTransactie.VoteStatus == StemTransactie.NINE_DIGITS)
				{
					if (iNumberOfAttempts.intValue() < iMaxAttempts)
					{
						request.setAttribute(
							CommandConstants.INLOG_ERROR,
							emf.getErrorMessage(
								ErrorConstants.VERIFY_STEM_CODE_ERR,
								null));
						redirect(
							request,
							response,
							CommandConstants.IDENTIFICATION_JSP);
						return;
					}
					else
					{
						ClientManager.updateCounter(
							ComponentType.WEB,
							CounterKeys.VERIFICATIE_MISLUKT);
						request.setAttribute(
							CommandConstants.ERROR_IN_REQUEST_KEY,
							emf.getErrorMessage(
								ErrorConstants.MAX_ATTEMPTS_EXCEEDED,
								null));
						redirect(
							request,
							response,
							CommandConstants.DEFAULT_ERROR_JSP);
						return;
					}
				}
				//if kiezer has already voted then redirect
				if (xStemTransactie.VoteStatus
					== StemTransactie.INVALID_CREDENTIALS)
				{
					if (iNumberOfAttempts.intValue() < iMaxAttempts)
					{
						request.setAttribute(
							CommandConstants.INLOG_ERROR,
							emf.getErrorMessage(
								ErrorConstants.KIEZER_INVALID_CREDENTIALS,
								null));
						redirect(
							request,
							response,
							CommandConstants.IDENTIFICATION_JSP);
						return;
					}
					else
					{
						/* update counter if attempts exceeded maxattempts */
						ClientManager.updateCounter(
							ComponentType.WEB,
							CounterKeys.VERIFICATIE_MISLUKT);
						request.setAttribute(
							CommandConstants.ERROR_IN_REQUEST_KEY,
							emf.getErrorMessage(
								ErrorConstants.MAX_ATTEMPTS_EXCEEDED,
								null));
						redirect(
							request,
							response,
							CommandConstants.DEFAULT_ERROR_JSP);
						return;
					}
				}
			}
		}
		catch (EPlatformException ep)
		{
			SystemProperties props = SystemProperties.getSystemProperties();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[UserPwdTicketServlet] EPlatformException: Forwarding Error to: "
					+ props.getProperty(
						"com.logica.eplatform.ticket.UserPwdErrorPage"));
			ErrorMessageFactory emf =
				ErrorMessageFactory.getErrorMessageFactory();
			request.setAttribute("ERROR", emf.getErrorMessage(ep));
			redirect(
				request,
				response,
				props.getProperty(
					"com.logica.eplatform.ticket.UserPwdErrorPage"));
			return;
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[UserPwdTicketServlet] Ticket obtained: " + ticket);
		// Check if a ticket is generated
		if (ticket == null)
		{
			/* set the message */
			String sMessage = "Onbekende technische fout.";
			if (xTicketResponse != null)
			{
				sMessage = xTicketResponse.getMessage();
			}
			/* set the verification message in the request */
			request.setAttribute("ERROR", sMessage);
			/* if not, redirect to error URL */
			redirect(
				request,
				response,
				props.getProperty(
					"com.logica.eplatform.error.DefaultErrorPage"));
			return;
		}
		// Store ticket in session
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[UserPwdTicketServlet] saving ticket in session");
		request.getSession(true).setAttribute(
			TicketConstants.TICKET_IN_SESSION,
			ticket);
		request.getSession(true).setAttribute(
			CommandConstants.STEMCODE,
			request.getParameter("USER"));
		request.getSession(true).setAttribute(
			CommandConstants.PASSWORD,
			request.getParameter("PWD"));
		// Redirect back to resource
		if (request
			.getSession(true)
			.getAttribute(TicketConstants.REQUESTED_RESOURCE_IN_SESSION)
			!= null)
		{
			String resource =
				(String) request.getSession(true).getAttribute(
					TicketConstants.REQUESTED_RESOURCE_IN_SESSION);
			request.getSession().removeAttribute(
				com
					.logica
					.eplatform
					.ticket
					.TicketConstants
					.REQUESTED_RESOURCE_IN_SESSION);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[UserPwdTicketServlet] redirecting to " + resource);
			redirect(request, response, resource);
		}
		/* otherwise redirect to the default resource page */
		else
		{
			redirect(
				request,
				response,
				props.getProperty(
					"com.logica.eplatform.error.DefaultResourceRedirectPage"));
		}
	}
}