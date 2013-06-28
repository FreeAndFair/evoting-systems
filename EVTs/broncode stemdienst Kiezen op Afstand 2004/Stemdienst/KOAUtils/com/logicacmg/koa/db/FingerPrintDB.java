/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.Fingerprint
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
  *  0.1.7		04-07-2003	MKu	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Timestamp;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.dataobjects.Fingerprint;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * This class checks for the static KR fingerprints 
 * which fingerprint is produced last. This one is needed for the 
 * check on the fingerprint.
 * 
 * @author KuijerM
 */
public class FingerPrintDB
{
	private static final String SELECT_MAX_ID_FINGERPRINT_FOR_STATE_OPEN =
		"select max (ID) as MAX_ID from koa01.krfingerprints where type = 1 and systemstatus = '"
			+ SystemState.OPEN
			+ "' ";
	private static final String SELECT_MAX_ID_FINGERPRINT_FOR_STATE_INIT =
		"select max (ID) as MAX_ID from koa01.krfingerprints where type = 1 and systemstatus = '"
			+ SystemState.INITIALIZED
			+ "' ";
	private static final String INSERT_KIESLIJST_FINGERPRINT =
		"INSERT INTO KOA01.KIESLIJSTFINGERPRINT (TIMESTAMP, TYPE, FINGERPRINT) VALUES (?, ?, ?) ";
	/**
	 * inserts the fingerprint of the kieslijst with all the candidates in the database
	 * 
	 * @param xFingerprint The fingerprint to save
	 * 
	 */
	public void insertKiesLijstFingerprint(Fingerprint xFingerprint)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[FingerPrintDB.insertKiesLijstFingerprint] ");
		if (xFingerprint.getFingerprintType()
			!= Fingerprint.KIESLIJST_KANDIDAATCODES_FINGERPRINT
			&& xFingerprint.getFingerprintType()
				!= Fingerprint.KIESLIJST_KIESLIJSTEN_FINGERPRINT
			&& xFingerprint.getFingerprintType()
				!= Fingerprint.KIESLIJST_LIJSTPOSITIES_FINGERPRINT)
		{
			throw new KOAException(ErrorConstants.WRONG_FINGERPRINT_TYPE);
		}
		/* init variables */
		DBUtils xDBUtils = null;
		Connection conn = null;
		PreparedStatement statement = null;
		ResultSet rsResult = null;
		try
		{
			/* init the DBUtils class */
			xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			conn = xDBUtils.getConnection();
			statement = conn.prepareStatement(INSERT_KIESLIJST_FINGERPRINT);
			/* set params */
			statement.setTimestamp(1, xFingerprint.getTimestamp());
			statement.setInt(2, xFingerprint.getFingerprintType());
			statement.setBytes(3, xFingerprint.getFingerprint());
			/* execute statement */
			statement.executeUpdate();
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Insert the kieslijst Fingerprint in db" };
			KOALogHelper.logErrorCode(
				"FingerPrintDB.insertKiesLijstFingerprint",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, params, sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closePreparedStatement(statement);
			xDBUtils.closeConnection(conn);
		}
		conn = null;
		statement = null;
		rsResult = null;
	}
	/**
	 * Returns the last known fingerprint for the kieslijst
	 * containing the candidates from the database.
	 * 
	 * @param iType The type for the fingerprint that should be retrieved
	 * 
	 * @return Fingerprint object containing the fingerprint.
	 * 
	 */
	public Fingerprint getLatestFingerprint(int iType) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[FingerPrintDB.getLatestKieslijstFingerprint] Start getting latest fingerprint for type "
				+ iType);
		String SELECT_CURRENT_KIESLIJST_FINGERPRINT =
			"SELECT TYPE as TYPE, TIMESTAMP as TIMESTAMP, FINGERPRINT as FINGERPRINT "
				+ "FROM KOA01.KIESLIJSTFINGERPRINT "
				+ "WHERE TYPE = "
				+ iType
				+ " AND ID = (SELECT MAX (ID) FROM KOA01.KIESLIJSTFINGERPRINT WHERE TYPE = "
				+ iType
				+ ") ";
		Fingerprint xFingerprint = new Fingerprint();
		/* init variables */
		DBUtils xDBUtils = null;
		Connection conn = null;
		Statement statement = null;
		ResultSet rsResult = null;
		/* loop through the result */
		try
		{
			/* init the DBUtils class */
			xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			statement = conn.createStatement();
			/* execute the select query */
			rsResult =
				statement.executeQuery(SELECT_CURRENT_KIESLIJST_FINGERPRINT);
			/* loop through the result */
			if (rsResult != null && rsResult.next())
			{
				/* getting free ID */
				Timestamp ts = rsResult.getTimestamp("TIMESTAMP");
				byte[] baBytes = rsResult.getBytes("FINGERPRINT");
				/* fill the fingerprint */
				xFingerprint.setFingerprint(baBytes);
				xFingerprint.setTimestamp(ts);
				xFingerprint.setFingerprintType(iType);
			}
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Get latest fingerprint for kieslijst" };
			KOALogHelper.logErrorCode(
				"FingerPrintDB.getStateForLastFingerprintByDataManager",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, params);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(statement);
			xDBUtils.closeConnection(conn);
		}
		conn = null;
		statement = null;
		rsResult = null;
		return xFingerprint;
	}
}