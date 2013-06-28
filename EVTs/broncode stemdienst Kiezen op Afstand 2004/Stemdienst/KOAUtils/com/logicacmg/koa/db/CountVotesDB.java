/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.CountVotesDB.java
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
  *  0.1.10		13-08-2003	MKu			New impl for other vote counts
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Vector;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.dataobjects.Kandidaat;
import com.logicacmg.koa.dataobjects.Partij;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class containing all the database actions for the vote count
 * 
 * @author KuijerM
 * 
 */
public class CountVotesDB
{
	private static final String SELECT_CANDIDATES =
		"select cast (KIESKRINGNUMMER as bigint) as KIESKRINGNUMMER, cast (KIESLIJSTNUMMER as bigint) as KIESLIJSTNUMMER, cast (POSITIENUMMER as bigint) as POSITIENUMMER, ACHTERNAAM, VOORLETTERS, ROEPNAAM, GESLACHT, WOONPLAATS from koa01.lijstposities ORDER BY KIESKRINGNUMMER, KIESLIJSTNUMMER, POSITIENUMMER ";
	private static final String SELECT_LISTS =
		"select KIESKRINGNUMMER, cast(kieslijstnummer as bigint) as KIESLIJSTNUMMER, LIJSTNAAM from koa01.kieslijsten ORDER BY KIESLIJSTNUMMER";
	private DBUtils xDBUtils = null;
	public CountVotesDB() throws KOAException
	{
		xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
	}
	/**
	 * Get the candidates in the system.
	 * 
	 * @return Vector containing the candidates in the system
	 * 
	 * @throws KOAException exception when something goes wrong
	 * 
	 */
	public Vector getCandidates() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[CountVotesDB.getCandidates] start get candidates");
		/* init variables */
		Vector vCandidates = new Vector();
		Kandidaat kandidaat = null;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the query */
			rsResult =
				xDBUtils.executeResultQuery(stmtStatement, SELECT_CANDIDATES);
			while (rsResult != null && rsResult.next())
			{
				kandidaat = new Kandidaat();
				kandidaat.kieskringnummer =
					rsResult.getString("KIESKRINGNUMMER");
				kandidaat.kieslijstnummer =
					rsResult.getString("KIESLIJSTNUMMER");
				kandidaat.positienummer = rsResult.getString("POSITIENUMMER");
				kandidaat.achterNaam = rsResult.getString("ACHTERNAAM");
				kandidaat.voorletters = rsResult.getString("VOORLETTERS");
				kandidaat.roepNaam = rsResult.getString("ROEPNAAM");
				kandidaat.geslacht = rsResult.getString("GESLACHT").charAt(0);
				kandidaat.woonplaats = rsResult.getString("WOONPLAATS");
				vCandidates.add(kandidaat);
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"CountVotesDB.getCandidates",
				"error getting candidates",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Select candidates" };
			KOALogHelper.logErrorCode(
				"CountVotesDB.getCandidates",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, params, sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* return the set of candidates */
		return vCandidates;
	}
	/**
	 * Get all the parties from the system
	 * 
	 * @return Vector containing all the parties in the system
	 * 
	 * @throws KOAException exception when something goes wrong
	 * 
	 */
	public Vector getLists() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[CountVotesDB.getLists] start get the lists...");
		/* init variables */
		Vector vLists = new Vector();
		Partij partij = null;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the query */
			rsResult = xDBUtils.executeResultQuery(stmtStatement, SELECT_LISTS);
			while (rsResult != null && rsResult.next())
			{
				partij = new Partij();
				partij.kieskringnummer = rsResult.getString("KIESKRINGNUMMER");
				partij.kieslijstnummer = rsResult.getString("KIESLIJSTNUMMER");
				partij.naam = rsResult.getString("LIJSTNAAM");
				/* add partij to the vector */
				vLists.add(partij);
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"CountVotesDB.getLists",
				"error getting lists",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Select lists" };
			KOALogHelper.logErrorCode(
				"CountVotesDB.getLists",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, params, sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* return the lists */
		return vLists;
	}
}