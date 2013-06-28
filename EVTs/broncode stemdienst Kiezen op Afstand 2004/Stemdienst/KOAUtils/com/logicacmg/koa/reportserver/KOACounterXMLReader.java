/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.KOACounterXMLReader.java
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
  *  0.1		13-05-2003	Mku			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver;
import java.io.IOException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;

import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.db.ControllerDB;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.db.ReportsDB;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.AbstractKOAReader;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Reader implementation to read the counter values of the past day
 * into XML format, for report perposes.
 * 
 * @author kuijerm
 */
public class KOACounterXMLReader extends AbstractKOAReader
{
	/* boolean values to indicate if some parts are already sent */
	boolean headerSent = false;
	boolean footerSent = false;
	boolean counterHeaderSent = false;
	boolean counterFooterSent = false;
	boolean counterContent = true;
	/* variables for data */
	String headerXML = null;
	Connection connKOA = null;
	PreparedStatement preCounters = null;
	ResultSet rstCounters = null;
	int rowcount = 0;
	int countergroup_id = -1;
	Timestamp tsStartPeriod = null;
	Timestamp tsEndPeriod = null;
	/**
	 * Constructor for the KOACounterXMLReader
	 */
	public KOACounterXMLReader(String sStartPeriod, String sEndPeriod)
		throws KOAException
	{
		super();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOACounterXMLReader] constructing the KOACounterXMLReader");
		GregorianCalendar cal = new GregorianCalendar();
		try
		{
			java.text.SimpleDateFormat sdf =
				new java.text.SimpleDateFormat("dd-MM-yyyy");
			Date dStart = new Date();
			Date dEnd = new Date();
			if (sStartPeriod != null && !sStartPeriod.trim().equals(""))
			{
				dStart = sdf.parse(sStartPeriod.trim());
			}
			if (sEndPeriod != null && !sEndPeriod.trim().equals(""))
			{
				dEnd = sdf.parse(sEndPeriod.trim());
			}
			cal.setTime(dEnd);
			cal.add(Calendar.DATE, 1);
			dEnd = cal.getTime();
			tsStartPeriod = new Timestamp(dStart.getTime());
			tsEndPeriod = new Timestamp(dEnd.getTime());
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KOACounterXMLReader] Could not parse the specified dates... Using default counters of today");
			throw new KOAException(
				ErrorConstants.COUNTER_XML_READER_VALIDATE_DATES,
				e);
		}
		try
		{
			/* set up the header XML */
			ReportsDB xReportsDB = new ReportsDB();
			headerXML =
				xReportsDB.getGlobalInformationHeader(
					tsStartPeriod,
					tsEndPeriod);
			/* get the connection for KOA */
			DBUtils xDBKOA =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KOA_NO_TRANS));
			connKOA = xDBKOA.getConnection();
			/* set up the query to get the right counter values */
			preCounters =
				connKOA.prepareStatement(ControllerDB.SELECT_COUNTER_HISTORY);
			preCounters.setTimestamp(1, tsStartPeriod);
			preCounters.setTimestamp(2, tsEndPeriod);
			/* get the resultset and the meta data for the resultset */
			rstCounters = preCounters.executeQuery();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"KOACounterXMLReader",
				"KOA Exception during construction of the KOACounterXMLReader",
				koae);
		}
		catch (SQLException sqle)
		{
			String[] params =
				{ "Getting counters and global header information" };
			KOALogHelper.logErrorCode(
				"KOACounterXMLReader",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"KOACounterXMLReader",
				ErrorConstants.ERR_READER_INIT,
				e);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOACounterXMLReader] KOACounterXMLReader constructed...");
	}
	/**
	 * Close everything that should be closed after reading
	 * 
	 * @throws IOException if something goes wrong closing the reader
	 * 
	 */
	public void close() throws IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAXMLDbReader.close] closing KOAXMLDbReader ");
		/* close everything that should be closed */
		try
		{
			rstCounters.close();
			preCounters.close();
			connKOA.close();
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KOACounterXMLDBReader.close] Could not close all open connections for counters");
		}
	}
	/**
	 * Get more data to read in the reader based on the blocksize
	 * 
	 * @param blocksize The blocksize to get. This is the minimum size of the String that is returned
	 * 
	 * @return String the next part of the xml data to read with the minimum length of the block size
	 * 
	 */
	protected String getMore(int blocksize)
	{
		String retString = "";
		/* first check if the header is already sent */
		if (!headerSent)
		{
			/* add the global xml tag if header or footer is provided */
			retString += "<REPORT>\n";
			retString += headerXML;
			headerSent = true;
		}
		/* after the header is sent, send the content from the database */
		else
		{
			/* check if the content header is sent */
			if (!counterHeaderSent)
			{
				retString = retString + "<COUNTERS>\n";
				counterHeaderSent = true;
			}
			try
			{
				/* as long as the string is smaller then the blocksize and
				 there is still content, add another row to the string */
				while ((retString.length() < blocksize) && counterContent)
				{
					/* check if there is another row */
					if (rstCounters.next())
					{
						/* add one to the row counter */
						rowcount++;
						/* check if this is the start of a new counter group */
						if (rstCounters.getInt("COUNTER_GROUP_ID")
							!= this.countergroup_id)
						{
							/* if it is not the first time add the closing tag of the counter group */
							if (this.countergroup_id != -1)
							{
								retString += "</COUNTERGROUP>";
							}
							/* add the start tag of the counter group */
							this.countergroup_id =
								rstCounters.getInt("COUNTER_GROUP_ID");
							retString += "<COUNTERGROUP ID=\""
								+ Integer.toString(countergroup_id)
								+ "\" ";
							retString += " ACTION=\""
								+ rstCounters.getString("ACTION")
								+ "\" ";
							retString += " TIMESTAMP=\""
								+ rstCounters
									.getTimestamp("TIMESTAMP")
									.toString()
								+ "\" >";
						}
						/* add the counter tag with all attributes and close the tag */
						retString += " <COUNTER COUNTER_ID=\""
							+ CounterKeys.getDutchTranslationForCounter(
								rstCounters.getString("COUNTER_ID"))
							+ "\" "
							+ " COUNTER_VALUE=\""
							+ rstCounters.getString("COUNTER_VALUE")
							+ "\" "
							+ " COMPONENT_TYPE=\""
							+ rstCounters.getString("COMPONENT_TYPE")
							+ "\" />\n";
					}
					else
					{
						/* if no more data is found, 
						always close the counter group 
						(expect when no group is ever found) */
						if (this.countergroup_id != -1)
						{
							retString += "</COUNTERGROUP>";
						}
						/* let the reader know there is no more content */
						counterContent = false;
						rowcount = 0;
					}
				}
			}
			catch (Exception e)
			{
				KOALogHelper.logErrorCode(
					"KOACounterXMLReader.getMore",
					ErrorConstants.ERR_READER_GET_MORE,
					e);
			}
			/* if there is no more data and the counter footer is not sent,
			send the counters end tag */
			if (!counterContent && !counterFooterSent)
			{
				retString = retString + "</COUNTERS>\n";
				counterFooterSent = true;
			}
		}
		/* if it is realy the end, only send the end tag of the report */
		if (!counterContent && !footerSent)
		{
			retString += "</REPORT>\n";
			footerSent = true;
		}
		else if (footerSent)
		{
			/* let the reader know there is really nothing more to send */
			retString = null;
		}
		return retString;
	}
}