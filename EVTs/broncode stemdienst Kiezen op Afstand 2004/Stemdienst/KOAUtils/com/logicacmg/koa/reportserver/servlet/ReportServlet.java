/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.report.ReportServlet.java
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
  *  0.1		12-05-2003	XUi			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.servlet;
import java.io.IOException;
import java.util.Enumeration;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.servlet.UtilServlet;
import com.logica.eplatform.ticket.Ticket;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.reportserver.command.ReportCommand;
import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.votecommands.CommandConstants;
public class ReportServlet extends UtilServlet
{
	/**
	 * doGet method of the Servlet
	 * Gets the Report from the Command that's saved in the Session and generates it's report.
	 * The report will be send to the screen.
	 */
	public void doGet(HttpServletRequest req, HttpServletResponse res)
		throws ServletException, java.io.IOException
	{
		ReportData reportData = null;
		try
		{
			// Get report  
			ReportCommand command =
				(ReportCommand) req.getAttribute(
					CommandConstants.COMMAND_IN_REQUEST_KEY);
			Report report = command.getReport();
			reportData = command.getReportData();
			/* Get the ticket */
			Ticket ticket = getTicket(req);
			/* Verify the roles against the reportdata */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ReportServlet.doGet] Verifying user roles");
			boolean bAuthorized = false;
			String role = null;
			Enumeration enum = reportData.getAuthorizedRoles().elements();
			while (enum.hasMoreElements())
			{
				role = (String) enum.nextElement();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportServlet.doGet] Checking role: " + role);
				if (ticket.hasRole(role))
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[ReportServlet.doGet] Valid role found!");
					bAuthorized = true;
					break;
				}
			}
			if (bAuthorized)
			{
				/* init the reportdata and the report */
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportServlet.doGet] initializing the report and reportdata");
				reportData.init();
				report.init();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportServlet.doGet] Set content-type "
						+ report.getContentType());
				res.setContentType(report.getContentType());
				if (report.getContentType().equals("text/xml"))
				{
					res.setHeader(
						"Content-Disposition",
						"inline; filename=\""
							+ report.getReportDataName()
							+ ".xml\"");
				}
				// Save the xml report with a specific name
				if (report.getContentType().equals("text/koaexport"))
				{
					res.setHeader(
						"Content-Disposition",
						"attachment; filename=\""
							+ report.getReportDataName()
							+ ".xml\"");
				}
				/* generate the report */
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportServlet.doGet] Generate");
				report.generate(reportData, res);
				/* flush the buffer of the response to make sure everything is sent to the client */
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportServlet.doGet] Flush outputstream");
				res.flushBuffer();
				/* make sure the report data is closed properly */
				reportData.close();
			}
			else
			{
				reportData.close();
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[ReportServlet.doGet] No valid roles found!, redirecting.");
				req.setAttribute(
					"ERROR",
					"U bent niet geautoriseerd om het rapport te bekijken.");
				redirect(
					req,
					res,
					props.getProperty(
						"com.logica.eplatform.error.DefaultErrorPage"));
			}
		}
		catch (EPlatformException ep)
		{
			/* close the report data if something goes wrong and log the error */
			if (reportData != null)
			{
				reportData.close();
			}
			KOALogHelper.logErrorCode(
				"ReportServlet",
				ErrorConstants.ERR_GENERATE_REPORT,
				ep);
			/* set the error message and redirect to the error jsp */
			try
			{
				req.setAttribute(
					"ERROR",
					com
						.logica
						.eplatform
						.error
						.ErrorMessageFactory
						.getErrorMessageFactory()
						.getErrorMessage(ep.getErrorCode(), ep.getParameters()));
			}
			catch (IOException ioe)
			{
				req.setAttribute(
					"ERROR",
					"Er heeft zich een probleem voorgedaan bij het ophalen van het rapport: "
						+ ep.getMessage());
			}
			redirect(
				req,
				res,
				props.getProperty(
					"com.logica.eplatform.error.DefaultErrorPage"));
		}
		catch (Exception e)
		{
			/* close the report data if something goes wrong and log the error */
			reportData.close();
			KOALogHelper.logErrorCode(
				"ReportServlet",
				ErrorConstants.ERR_GENERATE_REPORT,
				e);
			/* set the error message and redirect to the error jsp */
			req.setAttribute(
				"ERROR",
				"Er heeft zich een probleem voorgedaan bij het ophalen van het rapport: "
					+ e.getMessage());
			redirect(
				req,
				res,
				props.getProperty(
					"com.logica.eplatform.error.DefaultErrorPage"));
		}
	}
	/**
	 * doPost method of the Servlet
	 * Gets the Report from the Command that's saved in the Session and generateds it's report.
	 * The report will be send to the screen.
	 */
	public void doPost(HttpServletRequest req, HttpServletResponse res)
		throws ServletException, java.io.IOException
	{
		doGet(req, res);
	}
}