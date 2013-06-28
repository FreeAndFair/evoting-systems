/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.TransactionCodeDB.java
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
  *  0.1.8		21-07-2003	KvdP		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Random;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.security.RandomGenerator;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class TransactionCodeDB responsible for getting and inserting
 * transactioncodes.
 * 
 * @author Klaas van der Ploeg
 */
public class TransactionCodeDB
{
	/* used to insert a new transactioncode */
	private static final String INSERT_TRANSACTIONCODE =
		"INSERT INTO KOA01.TRANSACTIONCODE (TRANSACTIENUMMER) VALUES (?)";
	/* used to get the next transactioncode from db */
	private static final String GETNEXT_TRANSACTIONCODE_SEARCH_FROM_START =
		"SELECT TRANSACTIENUMMER FROM KOA01.TRANSACTIONCODE WHERE ALREADYUSED IS NULL OR ALREADYUSED!='Y' FETCH FIRST 1 ROW ONLY";
	private static final String UPDATENEXT_TRANSACTIONCODE =
		"UPDATE KOA01.TRANSACTIONCODE SET ALREADYUSED='Y' WHERE TRANSACTIENUMMER=?";
	/* used to remove transactioncodes */
	private static final String GET_TRANSACTIONCODE_WINDOW_FIRST =
		"SELECT TRANSACTIENUMMER FROM KOA01.TRANSACTIONCODE ORDER BY TRANSACTIENUMMER FETCH FIRST ";
	private static final String GET_TRANSACTIONCODE_WINDOW_SECOND =
		" ROWS ONLY";
	private static final String DELETE_TRANSACTIONCODES =
		"DELETE FROM KOA01.TRANSACTIONCODE WHERE TRANSACTIENUMMER BETWEEN ? AND ?";
	/* A random generator to get a list of random transactioncodes from the database     */
	/* The TRANSACTION_START_STRING is used in the random generator to pick a number     */
	/* between 0 and TRANSACTION_START_STRING                                            */
	/* The result is used as input in the GETNEXT_TRANSACTIONCODE_SEARCH_FROM_RANDOM_POS */
	private static final int RANDOM_BEGIN = 10;
	private static final int RANDOM_END = 100;
	private static final Random randomGenerator = new Random();
	public static void removeTransactionCodes() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TransactionCodeDB.removeTransactionCodes] start removing transactioncodes");
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR));
		/* get number of rows at a time (reuse same property) */
		int iTransactionCodeDelete =
			TechnicalProps.getIntProperty(TechnicalProps.KIEZER_DELETE);
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		PreparedStatement xPreDelete = null;
		ResultSet rs = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			/* setup the prepared statement */
			xPre =
				conn.prepareStatement(
					TransactionCodeDB.GET_TRANSACTIONCODE_WINDOW_FIRST
						+ iTransactionCodeDelete
						+ TransactionCodeDB.GET_TRANSACTIONCODE_WINDOW_SECOND);
			boolean recordsLeft = true;
			while (recordsLeft)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[TransactionCodeDB.removeTransactionCodes] Get a new window");
				/* get results */
				rs = xPre.executeQuery();
				if (rs.next())
				{
					/* get first record */
					String txCodeStart = rs.getString(1);
					String txCodeEnd = txCodeStart;
					while (rs.next())
					{
						txCodeEnd = rs.getString(1);
					}
					/* delete the found records */
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[TransactionCodeDB.removeTransactionCodes] Delete "
							+ iTransactionCodeDelete
							+ " records in this window");
					/* prepare the delete statement */
					xPreDelete =
						conn.prepareStatement(
							TransactionCodeDB.DELETE_TRANSACTIONCODES);
					xPreDelete.setString(1, txCodeStart);
					xPreDelete.setString(2, txCodeEnd);
					/* delete the records */
					xPreDelete.executeUpdate();
				}
				else
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[TransactionCodeDB.removeTransactionCodes] No records left");
					recordsLeft = false;
				}
			}
		}
		/* catch all the other errors concerning SQL */
		catch (SQLException sqle)
		{
			KOALogHelper.logErrorCode(
				"TransactionCodeDB.removeTransactionCodes",
				ErrorConstants.ERR_SQL,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rs);
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closePreparedStatement(xPreDelete);
			xDBUtils.closeConnection(conn);
		}
	}
	/**
	 * Inserts a new transactioncode in the database.
	 * 
	 * @throws KOAException if it failed to insert a new transactioncode
	 */
	public static void insertNewTransactionCodes(int nrOfCodes)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TransactionCodeDB.insertTransactionCodes] start generating "
				+ nrOfCodes
				+ " new transactioncodes");
		RandomGenerator generator = RandomGenerator.getInstance();
		/* get max number of attempts */
		int maxCreateAttempts =
			TechnicalProps.getIntProperty(TechnicalProps.MAX_RANDOM_ATTEMPTS);
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			/* setup the prepared statement */
			xPre =
				conn.prepareStatement(TransactionCodeDB.INSERT_TRANSACTIONCODE);
			/* insert a lot of codes at once */
			for (int i = 0; i < nrOfCodes; i++)
			{
				int attemptCount = 0;
				boolean succesfull = false;
				while (!succesfull && attemptCount <= maxCreateAttempts)
				{
					attemptCount++;
					try
					{
						/* generate the transactioncode */
						String txCode = generator.getTransactieCode();
						xPre.setString(1, txCode);
						/* execute the statement */
						xPre.executeUpdate();
						/* we finally managed to generate a unique transactioncode :-) */
						succesfull = true;
					}
					catch (SQLException sqle)
					{
						KOALogHelper.log(
							KOALogHelper.INFO,
							"Duplicate transactioncode. Attempt "
								+ attemptCount
								+ " of "
								+ maxCreateAttempts);
					}
				}
				/* give up */
				if (!succesfull)
				{
					throw new KOAException(
						"Failed to insert new transactioncode, giving up after "
							+ maxCreateAttempts
							+ " attempts");
				}
			}
		}
		/* catch all the other errors concerning SQL */
		catch (SQLException sqle)
		{
			KOALogHelper.logErrorCode(
				"TransactionCodeDB.insertTransactionCode",
				ErrorConstants.ERR_SQL,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, sqle);
		}
		finally
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[TransactionCodeDB.insertTransactionCodes] end generating transactioncodes");
			/* close everything */
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
	}
	/**
	 * Returns the next transactioncode from the database.
	 * 
	 * This method must be called from a transaction which
	 * has the table lock set to serializable.
	 * 
	 * @return String the next transactioncode (which is marked as used)
	 * 
	 * @throws KOAException if it failed to get the next transactioncode
	 */
	public static String getNextTransactionCode() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[TransactionCodeDB.getNextTransactionCode] start getting the next transactioncode (and marking it as used)");
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		ResultSet rs = null;
		boolean transactionCodeFound = false;
		String startString = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			/*
			 * First we randomly try to get a transaction code.
			 * If we find none we will start searching from the beginning
			 */
			int random_int =
				randomGenerator.nextInt(RANDOM_END - RANDOM_BEGIN)
					+ RANDOM_BEGIN;
			String sql_string =
				"SELECT TRANSACTIENUMMER FROM KOA01.TRANSACTIONCODE WHERE (ALREADYUSED IS NULL OR ALREADYUSED != 'Y') AND TRANSACTIENUMMER LIKE '"
					+ random_int
					+ "%' FETCH FIRST 1 ROW ONLY";
			xPre = conn.prepareStatement(sql_string);
			rs = xPre.executeQuery();
			if (rs.next() == true)
			{
				transactionCodeFound = true;
			}
			else
			{
				/* setup the prepared statement */
				xPre =
					conn.prepareStatement(
						TransactionCodeDB
							.GETNEXT_TRANSACTIONCODE_SEARCH_FROM_START);
				/* execute query to get the transactioncode */
				rs = xPre.executeQuery();
				if (rs.next() == true)
				{
					transactionCodeFound = true;
				}
			}
			/* did we get any records? */
			if (transactionCodeFound == true)
			{
				String txCode = rs.getString(1);
				/* prepare update statement */
				xPre =
					conn.prepareStatement(
						TransactionCodeDB.UPDATENEXT_TRANSACTIONCODE);
				/* set the update statement */
				xPre.setString(1, txCode);
				/* execute the update */
				xPre.executeUpdate();
				/* return transactioncode */
				return txCode;
			}
			else
			{
				throw new KOAException("There is no transactioncode left to fetch. All are used, or none are present.");
			}
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			KOALogHelper.logErrorCode(
				"TransactionCodeDB.getNextTransactionCode",
				ErrorConstants.ERR_SQL,
				sqle);
			throw new KOAException(ErrorConstants.ERR_SQL, sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rs);
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
	}
}