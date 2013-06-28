/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.report.ReportFactory.java
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
package com.logicacmg.koa.reportserver.report;
import java.io.IOException;
import java.util.Properties;
import java.util.StringTokenizer;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.report.ReportContext;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Reportfactory to provide the reports from the configuration
 * based on the report name.
 * 
 * @author uiterlix
 */
public class ReportFactory
{
	static private ReportFactory instance = null;
	private Properties globalProperties = new Properties();
	private java.util.Hashtable reports = new java.util.Hashtable();
	/**
	 * Private constructor for the report factory
	 */
	private ReportFactory()
	{
	}
	/**	
	 * @param name the name of the report to get
	 *  
	 * @return Report
	 * 
	 * @throws KOAException when the report can not be found
	 */
	public Report getReport(String name) throws KOAException
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[ReportFactory] getReport");
		Report report = (Report) reports.get(name);
		if (report == null)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ReportFactory] getReport: Report " + name + " not found.");
			throw new KOAException(
				ErrorConstants.REPORT_NO_SUCH_REPORT,
				new String[] { name });
		}
		return report;
	}
	/**
	 *  @return ReportFactory
	 */
	public static ReportFactory getReportFactory()
		throws com.logica.eplatform.error.EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ReportFactory] getReportFactory");
		if (instance == null)
		{
			instance = new ReportFactory();
			instance.init();
		}
		return instance;
	}
	/**
	 * Initalizes the ReportFactory
	 * 
	 * @throws EPlatformException when something goes wrong 
	 */
	private void init() throws EPlatformException
	{
		try
		{
			globalProperties.load(
				this.getClass().getResourceAsStream("/report.properties"));
			preloadReports();
		}
		catch (IOException ioe)
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ReportFactory] IOException while reading properties.");
			throw new EPlatformException(
				ErrorConstants.REPORT_PRELOAD_REPORTS,
				ioe);
		}
	}
	/**
	 * preloads the reports.
	 * 
	 * @throws EPlatformException
	 */
	private void preloadReports() throws EPlatformException
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[ReportFactory] preloadReports");
		try
		{
			StringTokenizer st =
				new StringTokenizer(
					(String) globalProperties.get("reports"),
					",");
			while (st.hasMoreTokens())
			{
				String name = (String) st.nextToken();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportFactory] preloading report " + name);
				Report report =
					(Report) Class
						.forName(globalProperties.getProperty(name + ".class"))
						.newInstance();
				report.setReportContext(
					new ReportContext(name, globalProperties));
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportFactory] init report " + name);
				reports.put(name, report);
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ReportFactory] report " + name + " initialized");
			}
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ReportFactory] "
					+ e.getClass().getName()
					+ "  while preloading reports: "
					+ e.getMessage());
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ReportFactory] propably bad configuration.");
			throw new EPlatformException(
				ErrorConstants.REPORT_PRELOAD_REPORTS,
				e);
		}
	}
}