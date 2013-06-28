/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.report.ReportContext.java
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
import java.util.Properties;

import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Context data class containing all the parameters 
 * that are provided for the report.
 * 
 * @author uiterlix
 */
public class ReportContext
{
	private String reportName;
	private Properties properties;
	/**
	 *  Constructor of the ReportContext
	 */
	protected ReportContext(String reportName, Properties properties)
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[ReportContext] constructor");
		this.reportName = reportName;
		this.properties = properties;
	}
	/**
	 * Gets the property for the specified key
	 * 
	 * @param key The key to get the property for
	 * 
	 * @return String the property for the key
	 * 
	 */
	String getProperty(String key)
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[ReportContext] getProperty");
		return properties.getProperty(reportName + "." + key);
	}
	/**
	 * Gets the reportname for the report
	 * 
	 * @return String The Report name
	 */
	String getReportName()
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[ReportContext] getReportName");
		return reportName;
	}
}