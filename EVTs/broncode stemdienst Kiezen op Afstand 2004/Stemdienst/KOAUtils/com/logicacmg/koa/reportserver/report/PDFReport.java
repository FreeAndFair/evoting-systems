/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.report.PDFReport.java
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
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.sql.Driver;

import javax.xml.transform.Result;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.sax.SAXResult;
import javax.xml.transform.stream.StreamSource;

import sun.net.dns.ResolverConfiguration.Options;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.reportserver.report.AbstractReport;
import com.logicacmg.koa.reportserver.report.Report;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Report implementation to generate PDF files
 * 
 * @author uiterlix
 */
public class PDFReport extends AbstractReport implements Report
{
	/**
	 * Inits the PDF report
	 * 
	 * @throws EPlatformException Exception during initialization
	 * 
	 * @see Report#init()
	 */
	public void init() throws EPlatformException
	{
		// set streamsource
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[PDFReport.init] Initializing streamsource: "
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
				"[PDFReport.init] Streamsource appears to be null");
			throw new EPlatformException(ErrorConstants.REPORT_PDF_NO_SOURCE);
		}
	}
	/**
	 * Generate the PDF report using the specified Report data object
	 * and the outputstream.
	 * 
	 * @param reportData The report data to get the data
	 * @param out The output stream to write the PDF report to
	 * 
	 * @throws EPlatformException exception during generation of the PDF report
	 * 
	 * @see Report#generate(ReportData, OutputStream)
	 */
	public void generate(ReportData reportData, OutputStream out)
		throws EPlatformException
	{
		try
		{
			/* Set config file to include additional fonts to support special character */
			File configFile =
				new File(
					TechnicalProps.getProperty(TechnicalProps.FOP_CONFIG_FILE));
			Options options = new Options(configFile);
			Driver driver = new Driver();
			driver.setRenderer(Driver.RENDER_PDF);
			driver.setOutputStream(out);
			TransformerFactory factory = TransformerFactory.newInstance();
			Transformer transformer = factory.newTransformer(getStreamSource());
			Result res = new SAXResult(driver.getContentHandler());
			transformer.transform(reportData.getStreamSource(), res);
		}
		catch (TransformerConfigurationException tce)
		{
			KOALogHelper.logErrorCode(
				"PDFReport.generate",
				ErrorConstants.ERR_REPORT_GENERATE_TRANSFORM_CONFIG,
				tce);
			throw new EPlatformException(
				ErrorConstants.REPORT_PDF_GENERATE,
				tce);
		}
		catch (TransformerException te)
		{
			KOALogHelper.logErrorCode(
				"PDFReport.generate",
				ErrorConstants.ERR_REPORT_GENERATE_TRANSFORM,
				te);
			throw new EPlatformException(
				ErrorConstants.REPORT_PDF_GENERATE,
				te);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"PDFReport.generate",
				ErrorConstants.ERR_REPORT_GENERATE_DEFAULT,
				e);
			throw new EPlatformException(ErrorConstants.REPORT_PDF_GENERATE, e);
		}
	}
	/**
	 * Generate the PDF report for the HTTP channel
	 * 
	 * @param reportData The report data to get the data
	 * @param res The HTTP response object to write the data to
	 * 
	 * @throws EPlatformException exception during generation of the PDF report
	 * 
	 * @see Report#generate(ReportData, HttpServletResponse)
	 */
	public void generate(ReportData reportData, HttpServletResponse res)
		throws EPlatformException
	{
		try
		{
			ByteArrayOutputStream bout = new ByteArrayOutputStream();
			generate(reportData, bout);
			byte[] content = bout.toByteArray();
			res.setContentLength(content.length);
			res.getOutputStream().write(content);
		}
		catch (IOException ioe)
		{
			String[] params = { "Request outputstream" };
			KOALogHelper.logErrorCode(
				"XMLReport.generate",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new EPlatformException(
				ErrorConstants.REPORT_PDF_GENERATE,
				ioe);
		}
	}
}