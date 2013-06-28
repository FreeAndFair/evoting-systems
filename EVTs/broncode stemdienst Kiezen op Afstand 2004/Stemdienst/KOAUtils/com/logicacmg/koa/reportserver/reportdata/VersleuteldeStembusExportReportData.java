/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.VersleuteldeStembusExportReportData.java
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
  *  0.2.0		22-10-2003	RB		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver.reportdata;
import javax.xml.transform.stream.StreamSource;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.db.ReportsDB;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.KOAXMLDbReader;
import com.logicacmg.koa.reportserver.reportdata.AbstractReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Report data for the encrypted esb result in XML format
 * 
 * @author BruinsR
 */
public class VersleuteldeStembusExportReportData
	extends AbstractReportData
	implements ReportData
{
	StreamSource streamSource = null;
	KOAXMLDbReader reader = null;
	/**
	 * @see ReportData#init()
	 */
	public void init() throws com.logica.eplatform.error.EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VersleuteldeStembusExportReportData.init] init election result export report data...");
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VersleuteldeStembusExportReportData.init] composing the global information header...");
		String sHeaderXML = null;
		try
		{
			ReportsDB xReportsDB = new ReportsDB();
			sHeaderXML = xReportsDB.getGlobalInformationHeader();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"VersleuteldeStembusExportReportData.init",
				"Error getting the global information header for election result export report data",
				koae);
			throw koae;
		}
		catch (Exception ex)
		{
			KOALogHelper.logErrorCode(
				"VersleuteldeStembusExportReportData.init",
				ErrorConstants.ERR_REPORT_DATA_INIT,
				ex);
			throw new KOAException(
				ErrorConstants.REPORT_PROCESVERBAAL_DEFAULT,
				ex);
		}
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VersleuteldeStembusExportReportData.init] setting stream source");
		try
		{
			String encoding =
				TechnicalProps.getProperty(
					TechnicalProps.KL_EXPORT_XML_ENCODING);
			reader =
				new KOAXMLDbReader(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_ESB_NO_TRANS),
					"KOA01",
					"ENCRYPTEDESB",
					null,
					sHeaderXML,
					null,
					encoding);
			streamSource = new StreamSource(reader);
			setStreamSource(streamSource);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"VersleuteldeStembusExportReportData.init",
				"could not find property in jndi properties, stream source not set",
				koae);
			throw koae;
		}
	}
	/**
	 * @see ReportData#close()
	 */
	public void close()
	{
		if (reader != null)
		{
			try
			{
				reader.close();
			}
			catch (Exception ioe)
			{
				String[] params = { "xml db reader" };
				KOALogHelper.logErrorCode(
					"VersleuteldeStembusExportReportData.close",
					ErrorConstants.ERR_COUNTERREADER_CLOSE,
					ioe);
			}
		}
	}
}