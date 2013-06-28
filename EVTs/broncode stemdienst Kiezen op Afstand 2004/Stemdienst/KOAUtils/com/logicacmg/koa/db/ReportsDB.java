/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.ReportsDB.java
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
package com.logicacmg.koa.db;
import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.rmi.RemoteException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.Date;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.io.TempFile;
import com.logicacmg.koa.scheduler.XMLProperties;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * All database actions concerning the reports are
 * concentrated here.
 */
public class ReportsDB
{
	private DBUtils xKOADBUtils = null;
	private DBUtils xKRDBUtils = null;
	private static final String SELECT_KIESKRINGEN =
		"SELECT KIESKRINGNUMMER, KIESKRINGNAAM FROM KOA01.KIESKRINGEN ";
	public static final String SELECT_STATISTICS =
		"select (SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE VERWIJDERD is null OR VERWIJDERD = 'N') as STEMMERS, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE VALIDLOGINS > 0 OR INVALIDLOGINS > 0) as TRY_TO_VOTE, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE REEDSGESTEMD = 'Y' and MODALITEIT = 'WEB') as ALREADY_VOTED_WEB, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE REEDSGESTEMD = 'Y' and MODALITEIT = 'TEL') as ALREADY_VOTED_TEL, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE REEDSGESTEMD != 'Y' and VERWIJDERD != 'Y') as NOT_VOTED_YET, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE ACCOUNTLOCKED = 'Y' and TIMESTAMPUNLOCK > (CURRENT TIMESTAMP) and VERWIJDERD != 'Y') as BLOCKED "
			+ "from sysibm.sysdummy1 FETCH FIRST 1 ROWS ONLY ";
	//The total number of voters who voted via the Web/WSM
	public static final String SELECT_KIEZERS_WSM =
		"select (SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE (VERWIJDERD is null OR VERWIJDERD = 'N') and MODALITEIT = 'WEB') as STEMMERS  from KOA01.KIEZERS FETCH FIRST 1 ROWS ONLY";
	//The total number of voters who voted via the Web/WSM
	public static final String SELECT_KIEZERS_TSM =
		"select (SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE (VERWIJDERD is null OR VERWIJDERD = 'N') and MODALITEIT = 'TEL') as STEMMERS  from KOA01.KIEZERS FETCH FIRST 1 ROWS ONLY";
	//The total number of voters in the ENCRYPTEDESB table
	public static final String SELECT_KIEZERS_ENCRYPTERESB =
		"SELECT COUNT(STEMNUMMER) AS STEMNUMMER FROM KOA01.ENCRYPTEDESB";
	//The total number of voters who didnt vote
	public static final String SELECT_KIEZERS_NON_VOTERS =
		"select (SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE (VERWIJDERD is null OR VERWIJDERD = 'N') and ( KOA01.KIEZERS.TIMESTAMPGESTEMD is null )) as STEMMERS  from KOA01.KIEZERS FETCH FIRST 1 ROWS ONLY";
	//The total number of voters in the system
	public static final String SELECT_TOTAAL_KIEZERS =
		"select (SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE VERWIJDERD is null OR VERWIJDERD = 'N') as TOTKIEZERS  from KOA01.KIEZERS FETCH FIRST 1 ROWS ONLY";
	//Counters with status IN_GESPREK
	public static final String SELECT_KIEZERS_INGESPREK =
		"SELECT count(KOA01.COUNTERS.COUNTER_ID) AS COUNTER_ID FROM   KOA01.COUNTERS WHERE   (( KOA01.COUNTERS.COUNTER_ID = 'IN_GESPREK' ))";
	//Counters with status AFGEBROKEN
	public static final String SELECT_KIEZERS_AFGEBROKEN =
		"SELECT count(KOA01.COUNTERS.COUNTER_ID) AS COUNTER_ID FROM   KOA01.COUNTERS WHERE   (( KOA01.COUNTERS.COUNTER_ID = 'AFGEBROKEN' ))";
	//Counters with status AFGEBROKEN
	public static final String SELECT_SYSTEM_STATE =
		"SELECT  KOA01.KOA_STATE.CURRENT_STATE AS CURRENT_STATE FROM  KOA01.KOA_STATE";
	//Counters with status GEBLOKKERD
	public static final String SELECT_GEBLOKKEERD =
		"SELECT count(KOA01.KIEZERS.STEMCODE) AS STEMCODECOUNT FROM KOA01.KIEZERS WHERE ((KOA01.KIEZERS.TIMESTAMPUNLOCK > CURRENT TIMESTAMP ))";
	// insert a new upload in reports table
	public static String INSERT_REPORTS =
		"INSERT INTO KOA01.REPORTS (id, type, timestamp, report) values (?, ?, ?, ?)";
	// select max id from reports table
	public static String SELECT_MAX_ID_REPORTS =
		"SELECT MAX(ID) FROM KOA01.REPORTS";
	/**
	 * Constructor for the reportsDB.
	 * 
	 */
	public ReportsDB() throws KOAException
	{
		xKOADBUtils =
			new DBUtils(
				JNDIProperties.getProperty(
					JNDIProperties.DATASOURCE_KOA_NO_TRANS));
		xKRDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(
					JNDIProperties.DATASOURCE_KR_NO_TRANS));
	}
	/**
	 * Gets the global header information XML String
	 * For the start and End timestamp the Timestamp difference is used from the audit log
	 * 
	 * @return String The XML representation of the global header information
	 * 
	 * @throws KOAException KOAException when something goes wrong
	 * 
	 */
	public String getGlobalInformationHeader() throws KOAException
	{
		return this.getGlobalInformationHeader(null, null, null);
	}
	/**
	 * Gets the global header information XML String
	 * For the start and End timestamp the Timestamp difference is used from the audit log
	 * 
	 * @param sCaller The caller ID of the information
	 * 
	 * @return String The XML representation of the global header information
	 * 
	 * @throws KOAException KOAException when something goes wrong
	 * 
	 */
	public String getGlobalInformationHeader(String sCaller)
		throws KOAException
	{
		return this.getGlobalInformationHeader(sCaller, null, null);
	}
	/**
	 * Gets the global header information XML String
	 * If start and End timestamp is null, the Timestamp difference is used from the audit log
	 * 
	 * @param tsStart The Start Timestamp to use in the global header information,
	 * @param tsEnd The end Timestamp to use in the global header information
	 * 
	 * @return String XML representation of the global header information
	 * 
	 * @throws KOAException KOAException when something goes wrong
	 * 
	 */
	public String getGlobalInformationHeader(
		Timestamp tsStart,
		Timestamp tsEnd)
		throws KOAException
	{
		return this.getGlobalInformationHeader(null, tsStart, tsEnd);
	}
	/**
	 * Gets the global header information XML String
	 * If start and End timestamp is null, the Timestamp difference is used from the audit log
	 * 
	 * @param sCaller The caller ID of the information
	 * @param tsStart The Start Timestamp to use in the global header information,
	 * @param tsEnd The end Timestamp to use in the global header information
	 * 
	 * @return String XML representation of the global header information
	 * 
	 * @throws KOAException KOAException when something goes wrong
	 * 
	 */
	public String getGlobalInformationHeader(
		String sCaller,
		Timestamp tsStart,
		Timestamp tsEnd)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ReportsDB.getGlobalInformationHeader] Start getting global information");
		String sHeaderXML = "";
		/* init variables */
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		try
		{
			/* set the first part of the xml */
			sHeaderXML += "<GLOBAAL ";
			sHeaderXML += " STEMBUREAU=\""
				+ FunctionalProps.getProperty(FunctionalProps.VOTING_OFFICE)
				+ "\" ";
			if (sCaller != null)
			{
				sHeaderXML += " VOORZITTER=\"" + sCaller + "\" ";
			}
			else
			{
				sHeaderXML += " VOORZITTER=\"Onbekend\" ";
			}
			sHeaderXML += " STATE=\""
				+ SystemState.getDutchTranslationForState(this.getState())
				+ "\" ";
			sHeaderXML += " VERKIEZING=\""
				+ FunctionalProps.getProperty(
					FunctionalProps.ELECTION_DESCRIPTION)
				+ "\" ";
			sHeaderXML += " PERIODE_START=\""
				+ FunctionalProps.getProperty(
					FunctionalProps.VOTING_START_DATE_TIME)
				+ "\" ";
			sHeaderXML += " PERIODE_EIND=\""
				+ FunctionalProps.getProperty(
					FunctionalProps.VOTING_END_DATE_TIME)
				+ "\" ";
			Date currentDate = new Date(System.currentTimeMillis());
			sHeaderXML += " CURTIME=\""
				+ this.getDateToString(currentDate)
				+ "\" ";
			/* end the global tag */
			sHeaderXML += ">\n";
			/* execute the query */
			conn = xKOADBUtils.getConnection();
			stmtStatement = conn.createStatement();
			rsResult =
				xKOADBUtils.executeResultQuery(
					stmtStatement,
					SELECT_KIESKRINGEN);
			sHeaderXML += "<KIESKRINGEN>\n";
			while (rsResult != null && rsResult.next())
			{
				String sKieskringNummer = rsResult.getString("KIESKRINGNUMMER");
				String sKieskringNaam = rsResult.getString("KIESKRINGNAAM");
				/* add the kieskring */
				sHeaderXML += "<KIESKRING NUMMER=\""
					+ sKieskringNummer
					+ "\" NAAM=\""
					+ sKieskringNaam
					+ "\" />\n";
			}
			sHeaderXML += "</KIESKRINGEN>\n";
			/* add the global end tag to close the globaal XML part */
			sHeaderXML += "</GLOBAAL>\n";
		}
		catch (Exception ex)
		{
			KOALogHelper.logErrorCode(
				"ReportDB.getGlobalInfo",
				ErrorConstants.ERR_REPORTS_DB_GLOBAL_HEADER,
				ex);
			throw new KOAException(ErrorConstants.REPORT_GLOBAL_HEADER, ex);
		}
		finally
		{
			/* close everything */
			xKOADBUtils.closeResultSet(rsResult);
			xKOADBUtils.closeStatement(stmtStatement);
			xKOADBUtils.closeConnection(conn);
		}
		/* return the Header xml */
		return sHeaderXML;
	}
	/**
	 * Gets the current state from the Controller
	 * 
	 * @return Current state
	 * 
	 */
	private String getState()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ReportsDB.getState] Start getting current state");
		String sState = com.logicacmg.koa.constants.SystemState.UNKNOWN;
		try
		{
			ControllerHome xControllerHome =
				ObjectCache.getInstance().getControllerHome();
			/* create remote instance from the home interface */
			Controller xController = xControllerHome.create();
			/* get the current counters */
			sState = xController.getCurrentState();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ReportsDB.getState",
				"KOA exception during lookup controller",
				koae);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"ReportsDB.getState",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"ReportsDB.getState",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
		}
		return sState;
	}
	/**
	 * Private function to convert the date object to 
	 * the right string representation.
	 * 
	 * @param dt The date to change
	 * 
	 * @return String the string representation
	 * 
	 */
	private String getDateToString(Date dt)
	{
		SimpleDateFormat sdfDay = new SimpleDateFormat("dd");
		SimpleDateFormat sdfMonth = new SimpleDateFormat("MM");
		SimpleDateFormat sdfRest = new SimpleDateFormat("yyyy HH:mm:ss");
		String sDay = sdfDay.format(dt);
		String sMonth = sdfMonth.format(dt);
		String sRest = sdfRest.format(dt);
		String sDutchMonth = "";
		try
		{
			int iMonth = Integer.parseInt(sMonth);
			switch (iMonth)
			{
				case 1 :
					sDutchMonth = "januari";
					break;
				case 2 :
					sDutchMonth = "februari";
					break;
				case 3 :
					sDutchMonth = "maart";
					break;
				case 4 :
					sDutchMonth = "april";
					break;
				case 5 :
					sDutchMonth = "mei";
					break;
				case 6 :
					sDutchMonth = "juni";
					break;
				case 7 :
					sDutchMonth = "juli";
					break;
				case 8 :
					sDutchMonth = "augustus";
					break;
				case 9 :
					sDutchMonth = "september";
					break;
				case 10 :
					sDutchMonth = "oktober";
					break;
				case 11 :
					sDutchMonth = "november";
					break;
				case 12 :
					sDutchMonth = "december";
					break;
				default :
					sDutchMonth = sMonth;
					break;
			}
		}
		catch (Exception e)
		{
			sDutchMonth = sMonth;
		}
		String returnValue = sDay + "-" + sDutchMonth + "-" + sRest;
		return returnValue;
	}
	/**
	 * Stors a XMLPropreties in report table in the database 
	 * 
	 * @param xProp XMLPropreties data object
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 * @param sType Type of report
	 */
	public static void storeReport(
		XMLProperties xProp,
		String sType,
		DBUtils xDB,
		Connection xConn)
		throws KOAException
	{
		PreparedStatement xPre = null;
		int iId = -1;
		try
		{
			// get max id + 1
			iId = getMaxReportID(xDB, xConn);
			// a byte array from the XMLProperties
			ByteArrayOutputStream xByteArray = new ByteArrayOutputStream();
			try
			{
				xProp.storeXML(xByteArray, "", "report");
			}
			catch (Exception e)
			{
				throw new KOAException(
					KOADataBeheerException.PROCESS_KIESLIJST,
					e);
			}
			// store the report in the database
			xPre = xConn.prepareStatement(ReportsDB.INSERT_REPORTS);
			xPre.setInt(1, iId);
			xPre.setString(2, sType);
			xPre.setTimestamp(3, new Timestamp(System.currentTimeMillis()));
			xPre.setBytes(4, xByteArray.toByteArray());
			xPre.executeUpdate();
		}
		catch (SQLException sqle)
		{
			String[] params = { "Insert report with ID " + iId };
			KOALogHelper.logErrorCode(
				"DataBeheerDB",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, sqle);
		}
		finally
		{
			xDB.closePreparedStatement(xPre);
		}
	}
	/**
	 * Stores tempory file in the database
	 * 
	 * @param xFile tempory file for storing readers-writers in the database
	 */
	public static void storeReport(TempFile xFile, String xType)
		throws KOAException
	{
		Connection conn = null;
		DBUtils xDB =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		try
		{
			conn = xDB.getConnection();
			ReportsDB.storeReport(xFile, xType, xDB, conn);
		}
		catch (KOAException koae)
		{
			throw koae;
		}
		catch (Exception e)
		{
			throw new KOAException(ErrorConstants.ERR_SQL, e);
		}
		finally
		{
			xDB.closeConnection(conn);
		}
	}
	/**
	 * Stores tempory file in the database
	 * 
	 * @param xFile tempory file for storing readers-writers in the database
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	public static void storeReport(
		TempFile xFile,
		String xType,
		DBUtils xDB,
		Connection xConn)
		throws KOAException
	{
		PreparedStatement xPre = null;
		int iId = -1;
		try
		{
			// get max id + 1
			iId = getMaxReportID(xDB, xConn);
			// insert TempFile in database
			xPre = xConn.prepareStatement(ReportsDB.INSERT_REPORTS);
			xPre.setInt(1, iId);
			xPre.setString(2, xType);
			xPre.setTimestamp(3, new Timestamp(System.currentTimeMillis()));
			InputStream is = new FileInputStream(xFile.getFile());
			xPre.setBinaryStream(4, is, (int) xFile.length());
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
			throw new KOAException(ErrorConstants.ERR_SQL, sqle);
		}
		catch (IOException ioe)
		{
			String[] params = { "File system" };
			KOALogHelper.logErrorCode(
				"DataBeheerDB",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.ERR_IO, ioe);
		}
		finally
		{
			xDB.closePreparedStatement(xPre);
		}
	}
	/**
	 * Gets max ID + 1 from reports database
	 * 
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	public static int getMaxReportID(DBUtils xDB, Connection xConn)
		throws KOAException
	{
		Statement stmt = null;
		ResultSet xRS = null;
		try
		{
			// get max id
			stmt = xConn.createStatement();
			xRS = xDB.executeResultQuery(stmt, ReportsDB.SELECT_MAX_ID_REPORTS);
			xRS.next();
			int iTempDataID = xRS.getInt(1);
			return ++iTempDataID;
		}
		catch (SQLException sqle)
		{
			String[] params = { "Select max report ID" };
			KOALogHelper.logErrorCode(
				"DataBeheerDB",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, sqle);
		}
		finally
		{
			xDB.closeResultSet(xRS);
			xDB.closeStatement(stmt);
		}
	}
}