/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.report.Report.java
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
import java.io.OutputStream;

import javax.xml.transform.stream.StreamSource;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.reportserver.report.ReportContext;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
/**
 * Report interface that must be implemented by all reports
 * 
 * @author uiterlix
 */
public interface Report
{
	/**
	 * Gets the stream source containing the data
	 * 
	 * @return StreamSource The stream source containing the data
	 */
	public StreamSource getStreamSource();
	/**
	 * Sets the ReportContext containing the parameters
	 * 
	 * @param context The context containing the parameters
	 */
	public void setReportContext(ReportContext context);
	/**
	 * Gets the reportContext containing the parameters for the report
	 * 
	 * @return ReportContext context containing the paramters
	 * 
	 */
	public ReportContext getReportContext();
	/**
	 * initialize the report
	 * 
	 * @throws EPlatformException when something goes wrong during initialization
	 * 
	 */
	public void init() throws EPlatformException;
	/**
	 * generate the report
	 * 
	 * @param reportData The report data to get the data from
	 * @param out The outpustream to write the data to
	 * 
	 */
	public void generate(ReportData reportData, OutputStream out)
		throws EPlatformException;
	/**
	 * Generate the report for the HTTP channel
	 * 
	 * @param reportData The report data to get the data from
	 * @param res The HTTP response object to write the data to
	 * 
	 */
	public void generate(ReportData reportData, HttpServletResponse res)
		throws EPlatformException;
	/**
	 * Sets the content type of the report
	 * 
	 * @param contentType The content type of the report
	 * 
	 */
	public void setContentType(String contentType);
	/**
	 * Gets the content type of the report
	 * 
	 * @return String the content type
	 * 
	 */
	public String getContentType();
	/**
	 * Gets the report data name for the report data object
	 * 
	 * @return String report data name
	 * 
	 */
	public String getReportDataName();
}