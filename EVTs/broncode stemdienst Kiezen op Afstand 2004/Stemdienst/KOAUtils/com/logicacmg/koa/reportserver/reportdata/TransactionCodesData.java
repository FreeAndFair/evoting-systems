/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.VerkiezingsUitslagExportReportData.java
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
  *  0.1.8		22-07-2003	KvdP		First implementation
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
 * Class responsible for getting the transactiondata
 * from the database
 * 
 * @author KvdP
 */
public class TransactionCodesData
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
			"[TransactionCodesData.init] init election result export report data...");
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TransactionCodesData.init] composing the global information header...");
		String sHeaderXML = null;
		try
		{
			ReportsDB xReportsDB = new ReportsDB();
			sHeaderXML = xReportsDB.getGlobalInformationHeader();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"TransactionCodesData.init",
				"Error getting the global information header for election result export report data",
				koae);
			throw koae;
		}
		catch (Exception ex)
		{
			KOALogHelper.logErrorCode(
				"TransactionCodesData.init",
				ErrorConstants.ERR_REPORT_DATA_INIT,
				ex);
			throw new KOAException(
				ErrorConstants.REPORT_PROCESVERBAAL_DEFAULT,
				ex);
		}
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TransactionCodesData.init] setting stream source");
		try
		{
			String encoding =
				TechnicalProps.getProperty(
					TechnicalProps.KL_EXPORT_XML_ENCODING);
			/* construct xml reader */
			reader =
				new KOAXMLDbReader(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KR_NO_TRANS),
					"KOA01",
					"KIEZERS",
					"TRANSACTIENUMMER",
					"TRANSACTIENUMMER",
					"REEDSGESTEMD='Y'",
					sHeaderXML,
					null,
					encoding);
			streamSource = new StreamSource(reader);
			setStreamSource(streamSource);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"TransactionCodesData.init",
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
					"TransactionCodesData.close",
					ErrorConstants.ERR_COUNTERREADER_CLOSE,
					ioe);
			}
		}
	}
}