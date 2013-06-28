/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.reportdata.BLOBResultSet.java
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
  *  0.1.9		26-07-2003	XUi			Performance ESB Fingerprints
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.Statement;

import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class for retrieving large resultsets containing blobs
 * 
 */
public class BLOBResultSet
{
	private int rsetsize = 0;
	private Connection xConn = null;
	private Statement xStatement = null;
	private ResultSet xRs = null;
	private String lastid = null;
	private boolean avail = true;
	private DBUtils xDBUtils = null;
	private String orderkey = null;
	private String datasource = null;
	private String schemaname = null;
	private String tablename = null;
	private String cols = null;
	/**
	 * Constructor
	 * 
	 * @param datasource datasource name
	 * @param schemaname schema name
	 * @param tablename table name
	 * @param orderkey	order key
	 * @param columns	columns
	 */
	public BLOBResultSet(
		String datasource,
		String schemaname,
		String tablename,
		String orderkey,
		String[] columns)
		throws KOAException
	{
		this.orderkey = orderkey;
		this.datasource = datasource;
		this.schemaname = schemaname;
		this.tablename = tablename;
		lastid = "0";
		this.rsetsize =
			TechnicalProps.getIntProperty(TechnicalProps.BLOB_RS_SIZE);
		cols = new String();
		if (columns.length > 0)
		{
			cols = columns[0];
			if (columns.length > 1)
				for (int i = 1; i < columns.length; i++)
				{
					cols = cols + "," + columns[i];
				}
		}
		try
		{
			xDBUtils = new DBUtils(datasource);
			xConn = xDBUtils.getConnection();
			xStatement = xConn.createStatement();
			String query =
				"SELECT "
					+ cols
					+ " FROM "
					+ schemaname
					+ "."
					+ tablename
					+ " ORDER BY "
					+ orderkey
					+ " FETCH FIRST "
					+ rsetsize
					+ " ROWS ONLY";
			xRs = xStatement.executeQuery(query);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[BlobResultSet.fetchMore()] " + query);
		}
		catch (Exception e)
		{
			throw new KOAException("Error in BLOBResultSet constructor.", e);
		}
	}
	private void fetchMore() throws KOAException
	{
		long startFetchMore = 0;
		try
		{
			System.out.println("Fetching more.... >" + lastid);
			xRs.close();
			xStatement.close();
			xConn.close();
			xConn = xDBUtils.getConnection();
			xStatement = xConn.createStatement();
			String query =
				"SELECT "
					+ cols
					+ " FROM "
					+ schemaname
					+ "."
					+ tablename
					+ " WHERE CAST("
					+ orderkey
					+ " AS BIGINT) > "
					+ lastid
					+ " ORDER BY "
					+ orderkey
					+ " FETCH FIRST "
					+ rsetsize
					+ " ROWS ONLY";
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[BlobResultSet.fetchMore()] " + query);
			xRs = xStatement.executeQuery(query);
		}
		catch (Exception e)
		{
			KOALogHelper.logError("BLOBResultSet", "Error in fetchmore()", e);
			throw new KOAException("Error in BLOBResultSet.fetchMore()", e);
		}
	}
	/**
	 * next() get the next record
	 * 
	 * @return next boolean
	 */
	public boolean next() throws KOAException
	{
		try
		{
			if (xRs.next())
			{
				avail = true;
				lastid = xRs.getString(1);
			}
			else
			{
				// see if we had all of the resultset
				if (avail == false)
				{
					xConn.close();
					return false;
				}
				avail = false;
				fetchMore();
				if (!next())
				{
					return false;
				}
			}
		}
		catch (Exception e)
		{
			KOALogHelper.logError("BLOBResultSet", "Error in next()", e);
			throw new KOAException("Error in BLOBResultSet.next()", e);
		}
		return true;
	}
	/**
	 * getBytes() Get the contents of the field as a byte[]. Note: this method doesn't work for timestamp fields.
	 * 
	 * @param fieldname		name of the field
	 * 
	 * @return	byte[]		byte[] with the contents of the field
	 */
	public byte[] getBytes(String fieldname) throws KOAException
	{
		try
		{
			return xRs.getBytes(fieldname);
		}
		catch (Exception e)
		{
			KOALogHelper.logError("BLOBResultSet", "Error in getBytes()", e);
			throw new KOAException("Error in BLOBResultSet.getBytes()", e);
		}
	}
	/**
	 * getString() Get the contents of the field as a string. Note: this method doesn't work for timestamp fields.
	 * 
	 * @param fieldname		name of the field
	 * 
	 * @return	byte[]		byte[] with the contents of the field
	 */
	public String getString(String fieldname) throws KOAException
	{
		try
		{
			return xRs.getString(fieldname);
		}
		catch (Exception e)
		{
			KOALogHelper.logError("BLOBResultSet", "Error in getString()", e);
			throw new KOAException("Error in BLOBResultSet.getString()", e);
		}
	}
	public void close()
	{
		try
		{
			xConn.close();
		}
		catch (Exception e)
		{
		}
	}
}