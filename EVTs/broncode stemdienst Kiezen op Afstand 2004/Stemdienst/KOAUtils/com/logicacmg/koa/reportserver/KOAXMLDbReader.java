/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.KOAXMLDbReader.java
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
import java.text.SimpleDateFormat;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.reportserver.AbstractKOAReader;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Generic Reader for tables in the database. Providing the table and schema
 * complete tables can be read and will be mapped to XML.
 * 
 * @author uiterlix
 */
public class KOAXMLDbReader extends AbstractKOAReader
{
	/* boolean values to indicate if some parts are already sent */
	boolean headerSent = false;
	boolean footerSent = false;
	boolean cont = true;
	/* variables for data */
	ResultSet rst = null;
	Connection conn = null;
	ResultSetMetaData metadata = null;
	String tableName = null;
	String headerXML = null;
	String footerXML = null;
	String encodingXML = null;
	int rowcount = 0;
	SimpleDateFormat timeFormat = new SimpleDateFormat("HH:mm:ss:SSS");
	/**
	 * Constructor for the KOAXMLDbReader
	 * 
	 * @param datasource The jnid name of the datasource to connect to
	 * @param schema The schema to find the database table in
	 * @param table The table to get the content from
	 * @param orderKey The column to order the result 
	 * @param headerXML The xml string to place in front of the database content
	 * @param footerXML The xml string to place in after the database content
	 * 
	 */
	public KOAXMLDbReader(
		String datasource,
		String schema,
		String table,
		String orderKey,
		String headerXML,
		String footerXML)
	{
		this(
			datasource,
			schema,
			table,
			orderKey,
			null,
			headerXML,
			footerXML,
			null);
	}
	/**
	 * Constructor for the KOAXMLDbReader
	 * 
	 * @param datasource The jnid name of the datasource to connect to
	 * @param schema The schema to find the database table in
	 * @param table The table to get the content from
	 * @param orderKey The column to order the result 
	 * @param headerXML The xml string to place in front of the database content
	 * @param footerXML The xml string to place in after the database content
	 * @param encoding The encoding to place in the header of the export
	 * 
	 */
	public KOAXMLDbReader(
		String datasource,
		String schema,
		String table,
		String orderKey,
		String headerXML,
		String footerXML,
		String encoding)
	{
		this(
			datasource,
			schema,
			table,
			orderKey,
			null,
			headerXML,
			footerXML,
			encoding);
	}
	/**
	 * Constructor for the KOAXMLDbReader
	 * 
	 * @param datasource The jnid name of the datasource to connect to
	 * @param schema The schema to find the database table in
	 * @param table The table to get the content from
	 * @param orderKey The column to order the result 
	 * @param whereClause The where clause for the database query. Free format after the 'where' keyword. Where keyword must not be specified.
	 * @param headerXML The xml string to place in front of the database content
	 * @param footerXML The xml string to place in after the database content
	 * @param encoding The encoding to place in the header of the export
	 * 
	 */
	public KOAXMLDbReader(
		String datasource,
		String schema,
		String table,
		String orderKey,
		String whereClause,
		String headerXML,
		String footerXML,
		String encoding)
	{
		this(
			datasource,
			schema,
			table,
			null,
			orderKey,
			whereClause,
			headerXML,
			footerXML,
			encoding);
	}
	/**
	 * Constructor for the KOAXMLDbReader
	 * 
	 * @param datasource The jnid name of the datasource to connect to
	 * @param schema The schema to find the database table in
	 * @param table The table to get the content from
	 * @param columns The columns to return in the result
	 * @param orderKey The column to order the result 
	 * @param whereClause The where clause for the database query. Free format after the 'where' keyword. Where keyword must not be specified.
	 * @param headerXML The xml string to place in front of the database content
	 * @param footerXML The xml string to place in after the database content
	 * @param encoding The encoding to place in the header of the export
	 * 
	 */
	public KOAXMLDbReader(
		String datasource,
		String schema,
		String table,
		String columns,
		String orderKey,
		String whereClause,
		String headerXML,
		String footerXML,
		String encoding)
	{
		super();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAXMLDbReader] constructing the KOAXMLDbReader");
		try
		{
			encodingXML = encoding;
			tableName = table;
			this.headerXML = headerXML;
			this.footerXML = footerXML;
			DBUtils xDBUtils = new DBUtils(datasource);
			conn = xDBUtils.getConnection();
			Statement stmt = conn.createStatement();
			/* use the parameters to compose the query */
			StringBuffer sbQuery = new StringBuffer("SELECT ");
			if (columns != null)
				sbQuery.append(columns);
			else
				sbQuery.append("* ");
			sbQuery.append(" FROM ").append(schema).append(".").append(table);
			if (whereClause != null)
				sbQuery.append(" WHERE ").append(whereClause);
			if (orderKey != null)
				sbQuery.append(" ORDER BY ").append(orderKey);
			/* execute the query and fill the metadata */
			rst = xDBUtils.executeResultQuery(stmt, sbQuery.toString());
			metadata = rst.getMetaData();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"KOAXMLDbReader",
				"KOA Exception during construction of the KOAXMLDbReader",
				koae);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"KOAXMLDbReader",
				ErrorConstants.ERR_READER_INIT,
				e);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAXMLDbReader] KOAXMLDbReader constructed...");
	}
	/**
	 * Close everything that should be closed when the reader is finished
	 * 
	 * @throws IOException when something goes wrong closing the reader
	 */
	public void close() throws IOException
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[] closing KOAXMLDbReader ()");
		try
		{
			rst.close();
			conn.close();
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KOAXMLDbReader.close] Could not close all open connections for db reader");
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
		if (headerSent == false)
		{
			/* add the global xml tag if header or footer is provided */
			if (headerXML != null || footerXML != null)
			{
				if (encodingXML != null)
				{
					retString += "<?xml version=\"1.0\" encoding=\""
						+ encodingXML
						+ "\"?>";
				}
				retString += "<REPORT>\n";
			}
			/* Construct and return header */
			if (headerXML != null)
			{
				retString = retString + headerXML + "\n";
			}
			retString = retString + "<TABLE NAME=\"" + tableName + "\">\n";
			headerSent = true;
		}
		else
		{
			try
			{
				while ((retString.length() < blocksize) && cont)
				{
					if (rst.next())
					{
						rowcount++;
						retString = retString + "	<ROW";
						for (int i = 1; i <= metadata.getColumnCount(); i++)
						{
							String value;
							String key = metadata.getColumnLabel(i);
							/* parse specific types */
							if (metadata.getColumnType(i) == Types.TIMESTAMP)
							{
								if (rst.getTimestamp(i) != null)
								{
									//value = String.valueOf(rst.getTimestamp(i).getTime());
									value =
										timeFormat.format(rst.getTimestamp(i));
								}
								else
								{
									value = "";
								}
							}
							else
							{
								/* fetch others as string */
								value = rst.getString(i);
							}
							retString =
								retString + " " + key + "=\"" + value + "\"";
						}
						retString = retString + "/>\n";
					}
					else
					{
						cont = false;
					}
				}
			}
			catch (Exception e)
			{
				KOALogHelper.logErrorCode(
					"KOAXMLDbReader.getMore",
					ErrorConstants.ERR_READER_GET_MORE,
					e);
			}
		}
		if ((cont == false) && (footerSent == false))
		{
			retString = retString + "</TABLE>\n";
			if (footerXML != null)
			{
				retString = retString + footerXML + "\n";
			}
			if (headerXML != null || footerXML != null)
			{
				retString += "</REPORT>\n";
			}
			footerSent = true;
		}
		else if (footerSent)
		{
			retString = null;
		}
		return retString;
	}
}