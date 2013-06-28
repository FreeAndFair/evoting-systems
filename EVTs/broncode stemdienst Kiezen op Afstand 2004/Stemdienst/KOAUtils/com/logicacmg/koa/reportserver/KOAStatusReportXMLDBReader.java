/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.KOAStatusReportXMLDBReader.java
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
  *  0.1		13-05-2003	XU			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver;
import java.io.IOException;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.Statement;
import java.sql.Types;

import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.db.ReportsDB;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.AbstractKOAReader;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * XML reader for the status report.
 * 
 * @author kuijerm
 */
public class KOAStatusReportXMLDBReader extends AbstractKOAReader
{
	/* boolean values to indicate if some parts are already sent */
	boolean headerSent = false;
	boolean footerSent = false;
	boolean statisticsHeaderSent = false;
	boolean statisticsFooterSent = false;
	boolean counterHeaderSent = false;
	boolean counterFooterSent = false;
	boolean statisticsContent = true;
	boolean counterContent = true;
	/* variables for sums */
	long lTSMLoginOpen = 0;
	long lWSMLoginOpen = 0;
	long lTSMLoginClosed = 0;
	long lWSMLoginClosed = 0;
	long lWSMValidLogins = 0;
	long lWSMInValidLogins = 0;
	long lTSMValidLogins = 0;
	long lTSMInValidLogins = 0;
	/* variables for data */
	Connection connKR = null;
	Statement stmtStatistics = null;
	Connection connKOA = null;
	Statement stmtCounters = null;
	ResultSet rstStatistics = null;
	ResultSetMetaData metadataStatistics = null;
	ResultSet rstCounters = null;
	ResultSetMetaData metadataCounters = null;
	String headerXML = null;
	String footerXML = null;
	int rowcount = 0;
	/**
	 * Constructor for the KOAStatusReportXMLDbReader
	 */
	public KOAStatusReportXMLDBReader(String sCaller)
	{
		super();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAStatusReportXMLDBReader] constructing the KOAStatusReportXMLDBReader");
		try
		{
			/* set up the utility classes for the two databases */
			DBUtils xDBKOA =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KOA_NO_TRANS));
			DBUtils xDBKR =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KR_NO_TRANS));
			/* get connection and statement for the KR database */
			connKR = xDBKR.getConnection();
			stmtStatistics = connKR.createStatement();
			/* get connection and statement for the KOA database */
			connKOA = xDBKOA.getConnection();
			stmtCounters = connKOA.createStatement();
			/* get the Database queries */
			String queryStatistics =
				com.logicacmg.koa.db.ReportsDB.SELECT_STATISTICS;
			String queryCounters =
				com.logicacmg.koa.db.ControllerDB.SELECT_CURRENT_COUNTERS;
			/* execute the queries on the KR database */
			rstStatistics =
				xDBKR.executeResultQuery(stmtStatistics, queryStatistics);
			metadataStatistics = rstStatistics.getMetaData();
			/* execute the queries on the KOA database */
			rstCounters =
				xDBKOA.executeResultQuery(stmtCounters, queryCounters);
			metadataCounters = rstCounters.getMetaData();
			try
			{
				/* get the global header information */
				ReportsDB xReportsDB = new ReportsDB();
				headerXML = xReportsDB.getGlobalInformationHeader(sCaller);
			}
			catch (KOAException koae)
			{
				KOALogHelper.logError(
					"ProcesVerbaalReportData.init",
					"Error getting the global information header for the proces verbaal report",
					koae);
			}
			catch (Exception ex)
			{
				KOALogHelper.logErrorCode(
					"ProcesVerbaalReportData.init",
					ErrorConstants.ERR_READER_INIT,
					ex);
			}
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"KOAStatusReportXMLDBReader",
				"KOA Exception during construction of the KOAStatusReportXMLDBReader",
				koae);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"KOAStatusReportXMLDBReader",
				ErrorConstants.ERR_READER_INIT,
				e);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAStatusReportXMLDBReader] KOAStatusReportXMLDBReader constructed...");
	}
	/**
	 * Close everything that should be closed when finished with the reader
	 * 
	 * @throws IOException when something goes wrong closing the reader
	 */
	public void close() throws IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAXMLDbReader.close] closing KOAXMLDbReader ");
		/* close the KR stuff */
		try
		{
			rstStatistics.close();
			stmtStatistics.close();
			connKR.close();
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KOAStatusReportXMLDBReader.close] Could not close all open connections for statistics");
		}
		/* close the KOA stuff */
		try
		{
			rstCounters.close();
			stmtCounters.close();
			connKOA.close();
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KOAStatusReportXMLDBReader.close] Could not close all open connections for counters");
		}
	}
	/**
	 * Gets more xml data for the reader from the database
	 * 
	 * @param blocksize The blocksize to get. This is the minimum size of the String that is returned
	 * 
	 * @return String the next part of the xml data to read with the minimum length of the block size
	 */
	protected String getMore(int blocksize)
	{
		String retString = "";
		/* first check if the header is already sent */
		if (!headerSent)
		{
			/* add the global xml tag if header or footer is provided */
			retString += "<REPORT>\n";
			/* add the header xml */
			if (headerXML != null)
			{
				retString += headerXML + "\n";
			}
			headerSent = true;
		}
		/* after the header is sent, send the statistics content */
		else
		{
			/* check if the statistics content is sent */
			if (statisticsContent)
			{
				/* check if the statistics header is sent */
				if (!statisticsHeaderSent)
				{
					statisticsHeaderSent = true;
				}
				try
				{
					/* as long as the string is smaller then the blocksize and
					 there is still statistics content, add another row to the string */
					while ((retString.length() < blocksize)
						&& statisticsContent)
					{
						if (rstStatistics.next())
						{
							rowcount++;
							/* loop through the meta data */
							for (int i = 1;
								i <= metadataStatistics.getColumnCount();
								i++)
							{
								String value;
								String key =
									metadataStatistics.getColumnLabel(i);
								/* parse specific types */
								if (metadataStatistics.getColumnType(i)
									== Types.TIMESTAMP)
								{
									if (rstStatistics.getTimestamp(i) != null)
									{
										value =
											rstStatistics
												.getTimestamp(i)
												.toString();
									}
									else
									{
										value = "";
									}
								}
								else
								{
									/* fetch others as string */
									value = rstStatistics.getString(i);
								}
								retString += "<"
									+ key
									+ " COUNTER_VALUE=\""
									+ value
									+ "\" />\n";
							}
						}
						/* no more rows found for statistics */
						else
						{
							statisticsContent = false;
							rowcount = 0;
						}
					}
				}
				catch (Exception e)
				{
					KOALogHelper.logErrorCode(
						"KOAStatusREportXMLDBReader.getMore",
						ErrorConstants.ERR_READER_GET_MORE,
						e);
				}
				/* check if the footer after the statistics content is already send */
				if (!statisticsContent && !statisticsFooterSent)
				{
					statisticsFooterSent = true;
				}
			}
			/* after all the statistics content is send, send the counters */
			else
			{
				/* check if the counters header is send */
				if (!counterHeaderSent)
				{
					counterHeaderSent = true;
				}
				try
				{
					/* as long as the string is smaller then the blocksize and
					 there is still counter content, add another row to the string */
					while ((retString.length() < blocksize) && counterContent)
					{
						if (rstCounters.next())
						{
							rowcount++;
							String counterID = null;
							String counterType = null;
							String counterValue = null;
							for (int i = 1;
								i <= metadataCounters.getColumnCount();
								i++)
							{
								String value = null;
								String key = metadataCounters.getColumnLabel(i);
								/* parse specific types */
								if (metadataCounters.getColumnType(i)
									== Types.TIMESTAMP)
								{
									if (rstCounters.getTimestamp(i) != null)
									{
										value =
											rstCounters
												.getTimestamp(i)
												.toString();
									}
									else
									{
										value = "";
									}
								}
								else
								{
									/* fetch others as string */
									value = rstCounters.getString(i);
									/* add the dutch translation for the column counter_id */
									if (metadataCounters
										.getColumnName(i)
										.equals("COUNTER_ID"))
									{
										counterID = value;
									}
									else if (
										metadataCounters.getColumnName(
											i).equals(
											"COMPONENT_TYPE"))
									{
										counterType = value;
									}
									else if (
										metadataCounters.getColumnName(
											i).equals(
											"COUNTER_VALUE"))
									{
										counterValue = value;
									}
									/* add sum of the logins */
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.TEL)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys.OPROEPEN_BEDRIJF))
									{
										lTSMLoginOpen =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.TEL)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys
												.OPROEPEN_BUITEN_BEDRIJF))
									{
										lTSMLoginClosed =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.WEB)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys.OPROEPEN_BEDRIJF))
									{
										lWSMLoginOpen =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.WEB)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys
												.OPROEPEN_BUITEN_BEDRIJF))
									{
										lWSMLoginClosed =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.TEL)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys.VERIFICATIE_GELUKT))
									{
										lTSMValidLogins =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.TEL)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys.VERIFICATIE_MISLUKT))
									{
										lTSMInValidLogins =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.WEB)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys.VERIFICATIE_GELUKT))
									{
										lWSMValidLogins =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
									if (metadataCounters
										.getColumnName(i)
										.equals("COMPONENT_TYPE")
										&& rstCounters.getString(i).equals(
											ComponentType.WEB)
										&& rstCounters.getString(
											"COUNTER_ID").equals(
											CounterKeys.VERIFICATIE_MISLUKT))
									{
										lWSMInValidLogins =
											rstCounters.getLong(
												"COUNTER_VALUE");
									}
								}
							}
							retString =
								retString
									+ "<"
									+ counterType
									+ "_"
									+ counterID
									+ " COUNTER_VALUE=\""
									+ counterValue
									+ "\""
									+ " />\n";
						}
						/* no more rows found for counters */
						else
						{
							counterContent = false;
							rowcount = 0;
						}
					}
				}
				catch (Exception e)
				{
					KOALogHelper.logErrorCode(
						"KOAStatusREportXMLDBReader.getMore",
						ErrorConstants.ERR_READER_GET_MORE,
						e);
				}
				/* check if the counters footer is send */
				if (!counterContent && !counterFooterSent)
				{
					retString += "<WEB_TEL_OPROEPEN_BEDRIJF COUNTER_VALUE=\""
						+ (lWSMLoginOpen + lTSMLoginOpen)
						+ "\" />";
					retString
						+= "<WEB_TEL_OPROEPEN_BUITEN_BEDRIJF COUNTER_VALUE=\""
						+ (lWSMLoginClosed + lTSMLoginClosed)
						+ "\" />";
					retString += "<WEB_TEL_VERIFICATIE_GELUKT COUNTER_VALUE=\""
						+ (lWSMValidLogins + lTSMValidLogins)
						+ "\" />";
					retString
						+= "<WEB_TEL_VERIFICATIE_MISLUKT COUNTER_VALUE=\""
						+ (lWSMInValidLogins + lTSMInValidLogins)
						+ "\" />";
					counterFooterSent = true;
				}
			}
		}
		/* if all the statistics content and header content is sent, 
		and the footer is not yet sent, send the footer. */
		if ((!counterContent && !statisticsContent) && (!footerSent))
		{
			if (footerXML != null)
			{
				retString += footerXML + "\n";
			}
			retString += "</REPORT>\n";
			footerSent = true;
		}
		/* if everything is sent, lett the reader know we are finished */
		else if (footerSent)
		{
			retString = null;
		}
		/* return the composed string */
		return retString;
	}
}