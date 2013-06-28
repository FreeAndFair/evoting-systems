/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.command.KOAReportCommand.java
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
  *  0.1		12-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.command;
import java.util.Enumeration;
import java.util.Properties;
import sun.security.krb5.internal.Ticket;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.command.ReportCommand;
import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.report.ReportFactory;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportDataFactory;
/**
 * The KOAReportCommand provides a KOA implementation of a command that can generate reports.
 * All actions are performed out side of the container.
 * 
 * @author KuijerM
 */
public class KOAReportCommand
	extends com.logica.eplatform.command.http.AbstractHttpCommand
	implements ReportCommand
{
	public static String CALLER = "caller";
	private java.lang.String RESULT_JSP;
	protected Properties parameters;
	private java.lang.String reportName;
	private java.lang.String reportDataName;
	private Report report;
	private ReportData reportData;
	/**
	 * executes the command.
	 * 
	 * @throws CommandException
	 * @throws EPlatformException
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[KOAReportCommand] execute");
	}
	/**
	 * returns the ErrorJSP
	 * 
	 * @return String	representing the error jsp
	 */
	public String getErrorJSP()
	{
		return "error.jsp";
	}
	/**
	 * returns the report, which was retrieved in the postExecution() method
	 * 
	 * @return Report
	 */
	public Report getReport()
	{
		LogHelper.trace(LogHelper.TRACE, "[KOAReportCommand] getReport");
		return report;
	}
	/**
	 * returns the ReportData, which was retrieved in the postExecution() method
	 * 
	 * @return ReportData
	 */
	public ReportData getReportData()
	{
		LogHelper.trace(LogHelper.TRACE, "[KOAReportCommand] getReportData");
		return reportData;
	}
	/**
	 * returns the resultJSP
	 * 
	 * @return String representing the resulting jsp
	 */
	public String getResultJSP()
	{
		return RESULT_JSP;
	}
	/**
	 * initializes the command. It tries to read the report name which was
	 * requested by the user.
	 * 
	 * @param request	an object representing the request to the servlet
	 */
	public void init(javax.servlet.http.HttpServletRequest request)
	{
		reportData = null;
		report = null;
		LogHelper.trace(LogHelper.TRACE, "[KOAReportCommand] init");
		RESULT_JSP = "/ReportRenderServlet";
		/* get the name of the chairman */
		String caller = "Onbekend";
		Ticket t =
			(Ticket) request.getSession(true).getAttribute(
				TicketConstants.TICKET_IN_SESSION);
		if (t != null)
		{
			caller = t.getUserID();
		}
		// get the reportname
		reportName = request.getParameter("report");
		// save all the parameters
		parameters = new Properties();
		Enumeration params = request.getParameterNames();
		String key;
		while (params.hasMoreElements())
		{
			key = (String) params.nextElement();
			parameters.put(key, request.getParameter(key));
		}
		//set the caller
		parameters.put(CALLER, caller);
	}
	/**
	 * postExecutes the command. This method actually instantiates the report and
	 * its accompanying reportdata.
	 * 
	 * @throws EPlatformException when something goes wrong
	 */
	public void postExecution()
		throws com.logica.eplatform.error.EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[KOAReportCommand] postExecution");
		try
		{
			LogHelper.trace(
				LogHelper.TRACE,
				"[KOAReportCommand] getting report data");
			ReportDataFactory reportDataFactory =
				ReportDataFactory.getReportDataFactory();
			reportData =
				reportDataFactory.getReportData(reportDataName, parameters);
		}
		catch (KOAException koae)
		{
			throw (EPlatformException) koae;
		}
		catch (Exception e)
		{
			LogHelper.trace(
				LogHelper.TRACE,
				"[KOAReportCommand] Exception in execute");
			throw new EPlatformException(ErrorConstants.REPORT_DATA_COMMAND, e);
		}
		try
		{
			LogHelper.trace(
				LogHelper.TRACE,
				"[KOAReportCommand] getting report");
			ReportFactory reportFactory = ReportFactory.getReportFactory();
			report = reportFactory.getReport(reportName);
		}
		catch (KOAException koae)
		{
			throw (EPlatformException) koae;
		}
		catch (Exception e)
		{
			LogHelper.trace(
				LogHelper.TRACE,
				"[KOAReportCommand] Exception in execute");
			throw new EPlatformException(ErrorConstants.REPORT_COMMAND, e);
		}
	}
	/**
	 * preExecutes the command.
	 */
	public void preExecution()
		throws com.logica.eplatform.error.EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[KOAReportCommand] preExecution");
		try
		{
			// get the report to get the reportDataName of the report
			ReportFactory reportFactory = ReportFactory.getReportFactory();
			Report rep = reportFactory.getReport(reportName);
			reportDataName = rep.getReportDataName();
		}
		catch (KOAException nsre)
		{
			LogHelper.trace(
				LogHelper.TRACE,
				"[KOAReportCommand] Exception in execute");
			throw (EPlatformException) nsre;
		}
	}
}