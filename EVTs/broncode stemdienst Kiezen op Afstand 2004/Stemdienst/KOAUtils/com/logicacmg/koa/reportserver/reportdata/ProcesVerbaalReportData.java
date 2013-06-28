/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.ProcesVerbaalReportData.java
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
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Properties;

import javax.xml.transform.stream.StreamSource;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.db.ReportsDB;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.KOAXMLDbReader;
import com.logicacmg.koa.reportserver.reportdata.AbstractReportData;
import com.logicacmg.koa.reportserver.reportdata.ReportData;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The report data class file for the Proces Verbaal 
 * in the KOA Application
 * 
 * @author KuijerM
 * 
 */
public class ProcesVerbaalReportData
	extends AbstractReportData
	implements ReportData
{
	StreamSource streamSource = null;
	KOAXMLDbReader reader = null;
	private Properties auditLogProperties = new Properties();
	private SimpleDateFormat dateFormat = new SimpleDateFormat("dd-MM-yyyy");
	private SimpleDateFormat timeFormat = new SimpleDateFormat("HH:mm");
	private SimpleDateFormat db2DateTimeFormat =
		new SimpleDateFormat("yyyyMMddHHmmss");
	private SimpleDateFormat DateTimeFormat =
		new SimpleDateFormat("dd-MM-yyyy HH:mm");
	/**
	 * @see ReportData#init()
	 */
	public void init() throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ProcesVerbaalReportData.init] init proces verbaal report data...");
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ProcesVerbaalReportData.init] composing the global information header...");
		String sHeaderXML = null;
		try
		{
			ReportsDB xReportsDB = new ReportsDB();
			sHeaderXML = xReportsDB.getGlobalInformationHeader();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ProcesVerbaalReportData.init",
				"Error getting the global information header for the proces verbaal report",
				koae);
			throw koae;
		}
		catch (Exception ex)
		{
			KOALogHelper.logErrorCode(
				"ProcesVerbaalReportData.init",
				ErrorConstants.ERR_REPORT_DATA_INIT,
				ex);
			throw new KOAException(
				ErrorConstants.REPORT_PROCESVERBAAL_DEFAULT,
				ex);
		}
		/* get and/or set variables */
		String whereClause = null;
		String selection = reportDataContext.getParameter("selection");
		String periodeStart = reportDataContext.getParameter("periode_start");
		String periodeStartTime =
			reportDataContext.getParameter("periode_start_time");
		String periodeEnd = reportDataContext.getParameter("periode_end");
		String periodeEndTime =
			reportDataContext.getParameter("periode_end_time");
		if (selection != null)
		{
			if (selection.equals("STATE_CHANGES") == true)
			{
				whereClause =
					" ACTION = '" + AuditEventListener.STATE_CHANGE + "'";
			}
			else if (selection.equals("DATA_MANAGEMENT") == true)
			{
				whereClause =
					" ACTION = '" + AuditEventListener.DATA_MANAGEMENT + "'";
			}
			else if (selection.equals("VOTER_EVENTS") == true)
			{
				whereClause =
					" ACTION = '"
						+ AuditEventListener.VOTER
						+ "' AND TYPE != 'Informatie'";
			}
			else if (selection.equals("OTHER") == true)
			{
				whereClause =
					" ACTION != '"
						+ AuditEventListener.STATE_CHANGE
						+ "' AND "
						+ " ACTION != '"
						+ AuditEventListener.DATA_MANAGEMENT
						+ "' AND "
						+ " ACTION != '"
						+ AuditEventListener.VOTER
						+ "'";
			}
			else if (selection.equals("COMPLETE") == true)
			{
				whereClause = null;
			}
		}
		String reportTitle = getReportTitleForSelection(selection);
		// add report title to the header
		sHeaderXML = sHeaderXML + createReportTitleXML(reportTitle);
		// create a datetime from seperate date and time
		Date dStart = createDate(periodeStart, periodeStartTime);
		Date dEnd = createDate(periodeEnd, periodeEndTime);
		if (whereClause == null)
		{
			whereClause = "";
		}
		else
		{
			whereClause = whereClause + " AND ";
		}
		// if one of the dates is wrong (null) the start and end date 
		// will be both set to now
		if (!((dStart != null) && (dEnd != null)))
		{
			dStart = new Date();
			dEnd = dStart;
		}
		// create where clause
		whereClause =
			whereClause
				+ " TIMESTAMP BETWEEN TIMESTAMP('"
				+ db2DateTimeFormat.format(dStart)
				+ "') AND TIMESTAMP('"
				+ db2DateTimeFormat.format(dEnd)
				+ "')";
		// add informtion on the date to the header
		sHeaderXML = sHeaderXML + createDateXML(dStart, dEnd);
		/* set stream source */
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ProcesVerbaalReportData.init] setting stream source");
		try
		{
			reader =
				new KOAXMLDbReader(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KOA_NO_TRANS),
					"KOA01",
					"AUDIT_LOG",
					"ROW_ID",
					whereClause,
					sHeaderXML,
					null,
					"UTF-8");
			streamSource = new StreamSource(reader);
			setStreamSource(streamSource);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ProcesVerbaalReportData.init",
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
				String[] params = { "reader" };
				KOALogHelper.logErrorCode(
					"StatusReportData.close",
					ErrorConstants.ERR_COUNTERREADER_CLOSE,
					ioe);
			}
		}
	}
	/**
	 * OR 22.3.648 Logbestand geen titel in rapport van de selectie
	 * returns the title for the auditlog selection
	 * 
	 * @param selection	The selection of the auditlog the title should return
	 */
	public String getReportTitleForSelection(String selection)
		throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ProcesVerbaalReportData.getReportTitleForSelection] get title for auditlog selection.");
		try
		{
			auditLogProperties.load(
				this.getClass().getResourceAsStream("/auditlog.properties"));
		}
		catch (IOException ioe)
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ProcesVerbaalReportData] IOException while reading properties.");
			throw new EPlatformException(ErrorConstants.AUDITLOG_LOAD, ioe);
		}
		return auditLogProperties.getProperty(selection);
	}
	/**
	 * creates the xml report title
	 * 
	 * @param selection	The selection of the auditlog the title should return
	 */
	public String createReportTitleXML(String reportTitle)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ProcesVerbaalReportData.createReportTitleXML] create xml for report title.");
		return "<PAGETITLE TITLE=\"" + reportTitle + "\" />\n";
	}
	/**
	 * creates the xml date tag
	 * @param dStart the start date
	 * @param dEnd the end date
	 * @return the xml date tag
	 */
	private String createDateXML(Date dStart, Date dEnd)
	{
		return "<DATE START=\""
			+ DateTimeFormat.format(dStart)
			+ "\" END=\""
			+ DateTimeFormat.format(dEnd)
			+ "\" />\n";
	}
	/**
	 * creates a dateTime from a date and a time
	 * if the date or the time is wrong null wil be returned
	 * @param periodeDate the date
	 * @param periodeTime the time
	 * @return the date 
	 */
	private Date createDate(String periodeDate, String periodeTime)
	{
		try
		{
			dateFormat.setLenient(false);
			timeFormat.setLenient(false);
			Date date;
			if (periodeDate != null && !periodeDate.trim().equals(""))
			{
				date = dateFormat.parse(periodeDate.trim());
				if (periodeTime != null && !periodeTime.trim().equals(""))
				{
					Date time = timeFormat.parse(periodeTime.trim());
					Calendar calendarDate = Calendar.getInstance();
					calendarDate.setTime(date);
					Calendar calendarTime = Calendar.getInstance();
					calendarTime.setTime(time);
					calendarDate.set(
						Calendar.HOUR_OF_DAY,
						calendarTime.get(Calendar.HOUR_OF_DAY));
					calendarDate.set(
						Calendar.MINUTE,
						calendarTime.get(Calendar.MINUTE));
					return calendarDate.getTime();
				}
			}
		}
		catch (java.text.ParseException e)
		{
		}
		return null;
	}
}