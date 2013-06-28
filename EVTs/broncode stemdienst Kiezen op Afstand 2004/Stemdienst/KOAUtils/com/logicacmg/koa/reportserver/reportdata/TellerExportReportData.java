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
 * Report data for the counters in XML format
 */
public class TellerExportReportData
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
			"[TellerExportReportData.init] init counters export report data...");
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TellerExportReportData.init] composing the global information header...");
		String sHeaderXML = null;
		try
		{
			ReportsDB xReportsDB = new ReportsDB();
			sHeaderXML = xReportsDB.getGlobalInformationHeader();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"TellerExportReportData.init",
				"Error getting the global information header for counters export report data",
				koae);
			throw koae;
		}
		catch (Exception ex)
		{
			KOALogHelper.logErrorCode(
				"TellerExportReportData.init",
				ErrorConstants.ERR_REPORT_DATA_INIT,
				ex);
			throw new KOAException(ErrorConstants.REPORT_EXPORT_DEFAULT, ex);
		}
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TellerExportReportData.init] setting stream source");
		try
		{
			String encoding =
				TechnicalProps.getProperty(
					TechnicalProps.KL_EXPORT_XML_ENCODING);
			reader =
				new KOAXMLDbReader(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KOA_NO_TRANS),
					"KOA01",
					"COUNTERS",
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
				"TellerExportReportData.init",
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
					"TellerExportReportData.close",
					ErrorConstants.ERR_COUNTERREADER_CLOSE,
					ioe);
			}
		}
	}
}