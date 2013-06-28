/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.report.XMLReport.java
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
import java.io.OutputStream;

import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.reportserver.report.AbstractReport;
import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * XSL report implementation to create reports in the HTML format.
 * Implements the report interface.
 * 
 * @author uiterlix
 */
public class XSLReport extends AbstractReport implements Report
{
	/**
	 * @see Report#init()
	 */
	public void init() throws EPlatformException
	{
		// set streamsource
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[XSLReport.init] Initializing streamsource: "
				+ getReportContext().getProperty("stylesheet"));
		source =
			new StreamSource(
				this.getClass().getResourceAsStream(
					getReportContext().getProperty("stylesheet")));
		contentType = getReportContext().getProperty("content-type");
		if (source == null)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[XSLReport.init] Streamsource appears to be null");
			throw new EPlatformException(ErrorConstants.REPORT_XSL_NO_SOURCE);
		}
	}
	/**
	 * Generates the XSL Report
	 * 
	 * @param reportData the reportdata to get the data from
	 * @param out The outputstream to write the data to
	 * 
	 * @throws EPlatformException exception when generating the report
	 * 
	 * @see Report#generate(ReportData, OutputStream)
	 */
	public void generate(ReportData reportData, OutputStream out)
		throws EPlatformException
	{
		try
		{
			TransformerFactory tFactory = TransformerFactory.newInstance();
			Transformer transformer =
				tFactory.newTransformer(getStreamSource());
			transformer.transform(
				reportData.getStreamSource(),
				new StreamResult(out));
		}
		catch (TransformerConfigurationException tce)
		{
			KOALogHelper.logErrorCode(
				"XSLReport.generate",
				ErrorConstants.ERR_REPORT_GENERATE_TRANSFORM_CONFIG,
				tce);
			throw new EPlatformException(
				ErrorConstants.REPORT_XSL_GENERATE,
				tce);
		}
		catch (TransformerException te)
		{
			KOALogHelper.logErrorCode(
				"XSLReport.generate",
				ErrorConstants.ERR_REPORT_GENERATE_TRANSFORM,
				te);
			throw new EPlatformException(
				ErrorConstants.REPORT_XSL_GENERATE,
				te);
		}
		/* Also catch the unexpected exceptions to make sure the reader gets closed */
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"XSLReport.generate",
				ErrorConstants.ERR_REPORT_GENERATE_DEFAULT,
				e);
			throw new EPlatformException(ErrorConstants.REPORT_XSL_GENERATE, e);
		}
	}
	/**
	 * Generates the XSL Report for the HTTP channel
	 * 
	 * @param reportData the reportdata to get the data from
	 * @param res The HTTP response to write the data to
	 * 
	 * @throws EPlatformException exception when generating the report
	 * 
	 * @see Report#generate(ReportData, HttpServletResponse)
	 */
	public void generate(ReportData reportData, HttpServletResponse res)
		throws EPlatformException
	{
		try
		{
			generate(reportData, res.getOutputStream());
		}
		catch (IOException ioe)
		{
			String[] params = { "Request outputstream" };
			KOALogHelper.logErrorCode(
				"XMLReport.generate",
				ErrorConstants.ERR_IO,
				params,
				ioe);
		}
	}
}