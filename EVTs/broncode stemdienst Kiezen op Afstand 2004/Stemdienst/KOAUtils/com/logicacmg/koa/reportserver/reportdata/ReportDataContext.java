/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.ReportDataContext.java
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
  *  0.1		09-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.reportdata;
import java.util.Properties;

import com.logica.eplatform.util.LogHelper;
/**
 * ReportData context used to provide all the parameters for the report data
 * 
 * @author KuijerM
 */
public class ReportDataContext
{
	private String reportName;
	private Properties properties;
	private Properties parameters;
	/**
	 * Constructs a new ReportDataContext.
	 * @param reportName	the report name
	 * @param properties	
	 * @param parameters
	 */
	protected ReportDataContext(
		String reportName,
		Properties properties,
		Properties parameters)
	{
		LogHelper.trace(LogHelper.TRACE, "[ReportDataContext] constructor");
		this.reportName = reportName;
		this.properties = properties;
		this.parameters = parameters;
	}
	/**
	 * Returns a parameter from the propertiesfile.
	 * 
	 * @return String (null when the parameter can not be found or no parameters
	 * 				   are given in the constructor)
	 */
	public String getParameter(String key)
	{
		LogHelper.trace(LogHelper.TRACE, "[ReportDataContext] getParameter");
		if (parameters == null)
		{
			return null;
		}
		else
		{
			return parameters.getProperty(key);
		}
	}
	/**
	 * Returns a parameter from the propertiesfile.
	 * 
	 * @return String (null when the property can not be found or no properties
	 * 				   are given in the constructor) 
	 */
	public String getProperty(String key)
	{
		LogHelper.trace(LogHelper.TRACE, "[ReportDataContext] getProperty");
		return properties.getProperty(reportName + "." + key);
	}
	/**
	 * Returns the reportdataname
	 * 
	 * @return String 
	 */
	public String getReportName()
	{
		LogHelper.trace(LogHelper.TRACE, "[ReportDataContext] getReportName");
		return reportName;
	}
}