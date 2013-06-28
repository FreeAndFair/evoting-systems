/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.AbstractReportData.java
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
package com.logicacmg.koa.reportserver.reportdata;
import java.util.Vector;

import javax.xml.transform.stream.StreamSource;

import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportDataContext;
/**
 * Abstract report data implementing the general methods and variables
 * for all Report data objects.
 * 
 * @author uiterlix
 */
public abstract class AbstractReportData implements ReportData
{
	protected transient ReportDataContext reportDataContext;
	protected StreamSource streamSource;
	private Vector authorizedRoles = null;
	/**
	 * Set the ReportDataContext for the Report
	 */
	public void setReportDataContext(ReportDataContext reportDataContext)
	{
		this.reportDataContext = reportDataContext;
	}
	/**
	 * Returns the ReportDataContext
	 */
	public ReportDataContext getReportDataContext()
	{
		return reportDataContext;
	}
	/**
	 * @see ReportData#getInputSource()
	 */
	public StreamSource getStreamSource()
	{
		return streamSource;
	}
	/**
	 * @see ReportData#getAuthorizedRoles()
	 */
	public Vector getAuthorizedRoles()
	{
		return authorizedRoles;
	}
	public void setAuthorizedRoles(Vector authorizedRoles)
	{
		this.authorizedRoles = authorizedRoles;
	}
	/**
	 * @see ReportData#setStreamSource(StreamSource)
	 */
	public void setStreamSource(StreamSource source)
	{
		this.streamSource = source;
	}
}