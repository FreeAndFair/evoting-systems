/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.servlet.KOAServlet.java
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
package com.logicacmg.koa.databeheer.servlet;
import java.io.IOException;
/**
 * The servlet that is used for all incoming requests that require 
 * a command. This servlet is called through different servlet aliases
 * that enables to differentation of commands.
 * Creation date: (07-04-2003 13:03:35)
 * @author: KuijerM
 */
public class KOADatabeheerServlet
	extends com.logica.eplatform.servlet.AbstractBaseServlet
{
	/* the instance of the commandfactory to get the commands */
	private com.logica.eplatform.command.http.HttpCommandFactory commandFactory;
	/** 
	 * Initializes the command factory.
	 */
	public void initCommandFactory()
	{
		// init factory
		//
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOADatabeheerServlet] initCommandFactory");
		commandFactory = KOACommandFactory.getHttpCommandFactory();
	}
	/**
	 * Initializes the Misc.
	 */
	public void initMisc()
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[KOADatabeheerServlet] initMisc");
	}
	/**
	 * Initializes the services.
	 */
	public void initServices()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOADatabeheerServlet] initServices");
		// initServices is no langer needed. Use the EventHandler or the KOALogHelper
	}
	/**
	 * Initializes the services.
	 * @param request The current Http request
	 * @param response the current Http response
	 */
	public void noTicket(
		HttpServletRequest request,
		HttpServletResponse response)
		throws IOException, ServletException
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[KOADatabeheerServlet] noTicket");
		/* filter the current requested location */
		Enumeration e = request.getParameterNames();
		StringBuffer buf = new StringBuffer();
		String element;
		while (e.hasMoreElements())
		{
			element = ((String) e.nextElement());
			buf.append(element + "=");
			buf.append(request.getParameter(element) + "&");
		}
		/* store the current requested location */
		request.getSession(true).setAttribute(
			com
				.logica
				.eplatform
				.ticket
				.TicketConstants
				.REQUESTED_RESOURCE_IN_SESSION,
			request.getServletPath() + "?" + buf.toString());
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOADatabeheerServlet] request saved in session");
		/* redirect the user to the ticket login page, to obtain a ticket */
		redirect(request, response, "/Ticket");
	}
	/**
	 * Process incoming HTTP GET requests
	 *
	 * @param request Object that encapsulates the request to the servlet
	 * @param response Object that encapsulates the response from the servlet
	 */
	public void performGetTask(
		javax.servlet.http.HttpServletRequest request,
		javax.servlet.http.HttpServletResponse response)
		throws javax.servlet.ServletException, java.io.IOException
	{
		performTask(request, response);
	}
	/**
	 * Process incoming HTTP POST requests
	 *
	 * @param request Object that encapsulates the request to the servlet
	 * @param response Object that encapsulates the response from the servlet
	 */
	public void performPostTask(
		javax.servlet.http.HttpServletRequest request,
		javax.servlet.http.HttpServletResponse response)
		throws javax.servlet.ServletException, java.io.IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOADatabeheerServlet] PerformPostTask Post");
		performTask(request, response);
	}
	/**
	 * Process incoming HTTP GET requests
	 *
	 * @param request Object that encapsulates the request to the servlet
	 * @param response Object that encapsulates the response from the servlet
	 */
	public void performTask(
		javax.servlet.http.HttpServletRequest request,
		javax.servlet.http.HttpServletResponse response)
		throws javax.servlet.ServletException, java.io.IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOADatabeheerServlet] performTask");
		HttpCommand command = null;
		try
		{
			/* Determine the command Factory */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet] Getting command from CommandFactory");
			command = commandFactory.getCommand(request);
			/* set command target */
			command.setCommandTarget(commandTarget);
			/* pre execute command */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet] Starting preExecution on Command:"
					+ command);
			command.preExecution();
			/* execute command */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet] Starting performExecute on Command: "
					+ command);
			command = (HttpCommand) command.performExecute(getTicket(request));
			/* post execute command */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet] Starting postExecution on Command: "
					+ command);
			command.postExecution();
			/* update the current http session */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet] Starting updateSession on Command: "
					+ command);
			command.updateSession(request.getSession());
			/* store the current command in the session */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet] Save command in Request on Command: "
					+ command);
			request.setAttribute(
				CommandConstants.COMMAND_IN_REQUEST_KEY,
				command);
			/* redirect the user to the result page for the command */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOADatabeheerServlet]: Forwarding to: "
					+ command.getResultJSP());
			redirect(request, response, command.getResultJSP());
		}
		catch (Exception e)
		{
			/* display errormessages made by the ErrorMessageFactory */
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KOADatabeheerServlet] A "
					+ e.getClass().getName()
					+ " was thrown with message: "
					+ e.getMessage());
			e.printStackTrace();
			ErrorMessageFactory emf =
				ErrorMessageFactory.getErrorMessageFactory();
			request.setAttribute("ERROR", emf.getErrorMessage(e));
			if (command == null)
			{
				SystemProperties props = SystemProperties.getSystemProperties();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KOADatabeheerServlet] EPlatformException: Forwarding Error to default errorpage ");
				redirect(
					request,
					response,
					props.getProperty(
						"com.logica.eplatform.error.DefaultErrorPage"));
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KOADatabeheerServlet] Forwarding Error to: "
						+ command.getErrorJSP());
				redirect(request, response, command.getErrorJSP());
			}
		}
	}
}