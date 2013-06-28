/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.report.AbstractReport.java
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
import javax.xml.transform.stream.StreamSource;

import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.report.ReportContext;
/**
 * Abstract Report implementing the general functions.
 * 
 * @author uiterlix
 */
public abstract class AbstractReport implements Report
{
	/* variables */
	protected ReportContext context = null;
	protected StreamSource source = null;
	protected String contentType = null;
	private String reportDataName = null;
	/**
	 * Gets the stream source containing the data
	 * 
	 * @return StreamSource the source containing the data
	 * 
	 * @see Report#getStreamSource()
	 */
	public StreamSource getStreamSource()
	{
		return source;
	}
	/**
	 * Sets the report context with parameters
	 * 
	 * @param context The report context
	 *  
	 * @see Report#setReportContext(ReportContext)
	 * 
	 */
	public void setReportContext(ReportContext context)
	{
		this.context = context;
	}
	/**
	 * gets the report context with parameters from the request
	 * 
	 * @return ReportContext containing parameteres
	 * 
	 * @see Report#getReportContext()
	 * 
	 */
	public ReportContext getReportContext()
	{
		return context;
	}
	/**
	 * Sets the content type
	 * 
	 * @param contentType The content type of the report
	 * 
	 * @see Report#setContentType(String)
	 * 
	 */
	public void setContentType(String contentType)
	{
		this.contentType = contentType;
	}
	/**
	 * Gets the Report content type
	 * 
	 * @return String the content type of the report
	 * 
	 * @see Report#getContentType()
	 * 
	 */
	public String getContentType()
	{
		return contentType;
	}
	/**
	 * Gets the Reportdata name
	 * 
	 * @return String the name of the report data used to get the data
	 *  
	 * @see Report#getReportData()
	 * 
	 */
	public String getReportDataName()
	{
		return getReportContext().getProperty("reportdata");
	}
}