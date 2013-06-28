/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.DataBeheerDB.java
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
  *  0.1		15-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;

import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.io.TempFile;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class containing all the query strings for the TempData plus
 * generic database action
 * 
 * @author MRo
 */
public class DataBeheerDB
{
	/**
	 * Private constructor to prevent instantiating
	 * 
	 */
	private DataBeheerDB()
	{
	}
	// select max id from tempdata table
	public static String SELECT_MAX_ID_TEMP_DATA =
		"SELECT MAX(ID) FROM KOA01.IMPORTTEMP";
	// select max id from tempdata table
	public static String SELECT_UPLOAD_TEMP_DATA =
		"SELECT importfile, action, type  FROM KOA01.IMPORTTEMP WHERE id = ?";
	// delete a row from tempdata table
	public static String DELETE_TEMP_DATA =
		"DELETE FROM KOA01.IMPORTTEMP WHERE id = ?";
	// insert a new upload in tempdata table
	public static String INSERT_TEMP_DATA =
		"INSERT INTO KOA01.IMPORTTEMP (id, action, type, timestamp, importfile) values (?, ?, ?, ?, ?)";
	// select all kielijstnummers form kieslijsten with no duplicates
	public static String SELECT_ALL_KIESLIJSTEN =
		"SELECT KIESLIJSTNUMMER FROM KOA01.KIESLIJSTEN GROUP BY KIESLIJSTNUMMER";
	// select all from kieskringen
	public static String SELECT_ALL_KIESKRINGEN =
		"SELECT KIESKRINGNUMMER, KIESKRINGNAAM FROM KOA01.KIESKRINGEN";
	// delete a row from tempdata table
	public static String DELETE_LIJSTPOSIES =
		"DELETE FROM KOA01.LIJSTPOSITIES WHERE KIESLIJSTNUMMER = ?";
	// delete a row from tempdata table
	public static String DELETE_KANDIDAATCODES =
		"DELETE FROM KOA01.KANDIDAATCODES WHERE KIESLIJSTNUMMER = ?";
	// delete the kieslijsten table
	public static String DELETE_KIESLIJSTEN = "DELETE FROM KOA01.KIESLIJSTEN";
	// select on the disticten table
	public static String SELECT_DISTRICTEN =
		"SELECT districtnummer, districtnaam FROM KOA01.DISTRICTEN WHERE kieskringnummer = ?";
	// select on the kieslijsten table
	public static String SELECT_KIESLIJSTEN =
		"SELECT kieslijstnummer, lijstnaam FROM KOA01.KIESLIJSTEN WHERE kieskringnummer = ? ORDER BY cast(kieslijstnummer as bigint)";
	// select on the lijstposities table
	public static String SELECT_LIJSTPOSITIES =
		"SELECT POSITIENUMMER, ACHTERNAAM, VOORLETTERS, ROEPNAAM, GESLACHT, WOONPLAATS FROM KOA01.LIJSTPOSITIES WHERE KIESKRINGNUMMER = ? AND KIESLIJSTNUMMER = ? order by cast(positienummer as bigint)";
	// select on the kandidaatcodes table
	public static String SELECT_KANDIDAATCODES =
		"SELECT KANDIDAATCODE FROM KOA01.KANDIDAATCODES WHERE KIESKRINGNUMMER = ? AND KIESLIJSTNUMMER = ? AND POSITIENUMMER = ?";
	// count the kieskingen
	public static String SELECT_COUNT_KIESKRINGEN =
		"SELECT count(kieskringnummer) from KOA01.KIESKRINGEN";
	// count the districten
	public static String SELECT_COUNT_DISTRICTEN =
		"SELECT count(districtnummer) from KOA01.DISTRICTEN";
	// count the kieslijsten
	public static String SELECT_COUNT_KIESLIJSTEN =
		"SELECT count(kieslijstnummer) from KOA01.KIESLIJSTEN";
	// count the lijstposities
	public static String SELECT_COUNT_LIJSTPOSITIES =
		"SELECT count(positienummer) from KOA01.LIJSTPOSITIES";
	// count the kandidaatcodes
	public static String SELECT_COUNT_KANDIDAATCODES =
		"SELECT count(kandidaatcode) from KOA01.KANDIDAATCODES";
	// count the kandidaatcodes
	public static String SELECT_COUNT_KIEZERS =
		"SELECT count(stemcode) from KOA01.KIEZERS where VERWIJDERD = 'N'";
	// count the kandidaatcodes
	public static String SELECT_KIEZERS_ID =
		"SELECT kiezeridentificatie, hashedwachtwoord, stemcode from KOA01.KIEZERS where VERWIJDERD = 'N' AND kieskringnummer = ? AND districtnummer = ?";
	// select type from import temp							
	public static String SELECT_TYPE_TEMP_DATA =
		"SELECT type, action FROM KOA01.IMPORTTEMP where id = ?";
	// delete kiezers							
	public static String DELETE_KIEZERS =
		"DELETE FROM KOA01.KIEZERS WHERE stemcode BETWEEN ? AND ?";
	/**
	 * selects a count rows from the database
	 * 
	 * @param sCount SQL select statement with the count
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 * 
	 * @throws KOAException	when the sql statement fails
	 */
	public static String selectCount(
		String sCount,
		DBUtils xDB,
		Connection xConn)
		throws KOAException
	{
		ResultSet xRsMax = null;
		PreparedStatement xPre = null;
		try
		{
			xPre = xConn.prepareStatement(sCount);
			xRsMax = xPre.executeQuery();
			xRsMax.next();
			return xRsMax.getString(1);
		}
		catch (SQLException sqle)
		{
			String[] params = { "Select count rows" };
			KOALogHelper.logErrorCode(
				"DataBeheerDB",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				sqle);
		}
		finally
		{
			xDB.closeResultSet(xRsMax);
			xDB.closePreparedStatement(xPre);
		}
	}
	/**
	 * Stores tempory file in the database
	 * 
	 * @param xFile tempory file for storing readers-writers in the database
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 * 
	 * @throws KOAException		when the upload fails
	 */
	public static void storeUpload(
		TempFile xFile,
		int tempdataId,
		String action,
		String contentType,
		Timestamp timeStamp,
		Connection xConn)
		throws KOAException
	{
		PreparedStatement xPre = null;
		int iId = -1;
		try
		{
			KOALogHelper.log(
				LogHelper.INFO,
				"[Upload] Get inputstream on: " + xFile.getFile().getName());
			InputStream is = new FileInputStream(xFile.getFile());
			xPre = xConn.prepareStatement(DataBeheerDB.INSERT_TEMP_DATA);
			xPre.setInt(1, tempdataId);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set action");
			xPre.setString(2, action);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set content type");
			xPre.setString(3, contentType);
			xPre.setTimestamp(4, timeStamp);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set binary stream");
			xPre.setBinaryStream(5, is, (int) xFile.length());
			KOALogHelper.log(LogHelper.INFO, "[Upload] Execute update");
			xPre.executeUpdate();
			is.close();
		}
		catch (SQLException sqle)
		{
			String[] params = { "Insert report with ID " + iId };
			KOALogHelper.logErrorCode(
				"DataBeheerDB",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				sqle);
		}
		catch (IOException ioe)
		{
			String[] params = { "File system" };
			KOALogHelper.logErrorCode(
				"DataBeheerDB",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
		finally
		{
			try
			{
				xPre.close();
			}
			catch (Exception e)
			{
			}
		}
	}
}