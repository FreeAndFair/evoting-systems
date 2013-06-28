/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.ControllerDB.java
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
  *  0.1		14-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
import java.security.PublicKey;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Timestamp;
import java.util.Enumeration;
import java.util.Vector;

import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.controller.subscription.ClientSubscription;
import com.logicacmg.koa.controller.subscription.ControlClientSubscription;
import com.logicacmg.koa.controller.subscription.ESBClientSubscription;
import com.logicacmg.koa.controller.subscription.KRClientSubscription;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOADBException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.Convertor;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class containing all the database actions for the controller
 * 
 * @author KuijerM
 * 
 */
public class ControllerDB
{
	public static String SELECT_CURRENT_COUNTERS =
		"SELECT COUNTERS.COUNTER_ID as COUNTER_ID, "
			+ "		COUNTERS.TIMESTAMP as TIMESTAMP, "
			+ "		COUNTERS.ACTION as ACTION, "
			+ "		COUNTERS.COMPONENT_TYPE as COMPONENT_TYPE, "
			+ "		SUM (COUNTERS.COUNTER_VALUE) as COUNTER_VALUE "
			+ "FROM 	KOA01.COUNTERS COUNTERS "
			+ "WHERE 	COUNTERS.COUNTER_GROUP_ID = ( SELECT MAX (COUNTERS2.COUNTER_GROUP_ID) "
			+ "									  FROM KOA01.COUNTERS COUNTERS2 ) "
			+ "GROUP BY COUNTER_ID, TIMESTAMP, ACTION, COMPONENT_TYPE "
			+ "ORDER BY COMPONENT_TYPE ";
	public static String SELECT_CURRENT_COUNTERS_STATUS_REPORT =
		"SELECT COUNTERS.COUNTER_ID as COUNTER_ID, "
			+ "		COUNTERS.ACTION as ACTION, "
			+ "		COUNTERS.COMPONENT_TYPE as COMPONENT_TYPE, "
			+ "		SUM (COUNTERS.COUNTER_VALUE) as COUNTER_VALUE "
			+ "FROM 	KOA01.COUNTERS COUNTERS "
			+ "WHERE 	COUNTERS.COUNTER_GROUP_ID = ( SELECT MAX (COUNTERS2.COUNTER_GROUP_ID) "
			+ "									  FROM KOA01.COUNTERS COUNTERS2 ) "
			+ "GROUP BY COUNTER_ID, ACTION, COMPONENT_TYPE "
			+ "ORDER BY COMPONENT_TYPE ";
	public static String SELECT_COUNTER_HISTORY =
		"SELECT 	COUNTERS.COUNTER_GROUP_ID as COUNTER_GROUP_ID, "
			+ "			COUNTERS.COUNTER_ID as COUNTER_ID, "
			+ "			COUNTERS.TIMESTAMP as TIMESTAMP, "
			+ "			COUNTERS.ACTION as ACTION, "
			+ "			COUNTERS.COMPONENT_TYPE as COMPONENT_TYPE, "
			+ "			SUM (COUNTERS.COUNTER_VALUE) as COUNTER_VALUE "
			+ "FROM 	KOA01.COUNTERS COUNTERS "
			+ "WHERE 	COUNTERS.TIMESTAMP > ? "
			+ "  AND 	COUNTERS.TIMESTAMP < ? "
			+ "GROUP BY COUNTER_GROUP_ID, COUNTER_ID, TIMESTAMP, ACTION, COMPONENT_TYPE "
			+ "ORDER BY COUNTER_GROUP_ID, COMPONENT_TYPE ";
	public static String SELECT_CURRENT_WEB_COUNTER =
		"SELECT COUNTERS.COUNTER_VALUE	"
			+ "FROM 	KOA01.COUNTERS COUNTERS "
			+ "WHERE 	COUNTERS.COUNTER_GROUP_ID = ( SELECT MAX (COUNTERS2.COUNTER_GROUP_ID) "
			+ "									  FROM KOA01.COUNTERS COUNTERS2 ) "
			+ "AND UPPER(COUNTERS.COUNTER_ID) = ? AND COUNTERS.COMPONENT_TYPE='WEB' ";
	private static String SELECT_COUNT_CANDIDATES =
		"SELECT COUNT (*) as COUNT " + "FROM KOA01.LIJSTPOSITIES ";
	private static String SELECT_FREE_ID =
		"SELECT MAX (INTERNAL.FREE_ID) as FREE_ID "
			+ "FROM KOA01.KOA_INTERNAL INTERNAL ";
	private static String UPDATE_FREE_ID =
		"UPDATE KOA01.KOA_INTERNAL SET FREE_ID = (FREE_ID + 1) ";
	private static String INSERT_KOA_INTERNAL_RECORD =
		"INSERT INTO KOA01.KOA_INTERNAL " + " (ID, FREE_ID) VALUES (0, 1) ";
	private static String SELECT_KOA_INTERNAL_ROWCOUNT =
		"SELECT COUNT (*) as COUNT FROM KOA01.KOA_INTERNAL ";
	private static String SELECT_SUBSCRIBER_LIST_ROWCOUNT =
		"SELECT COUNT (*) as COUNT FROM KOA01.SUBSCRIBER_LIST ";
	private static String INSERT_CLIENT_SUBSCRIPTION =
		"INSERT INTO KOA01.SUBSCRIBER_LIST "
			+ "(COMPONENT_ID, JNDI_NAME, COMPONENT_TYPE, CONTEXT, CONTEXT_FACTORY) VALUES (?, ?, ?, ?, ?) ";
	private static String DELETE_CLIENT_SUBSCRIPTION =
		"DELETE FROM KOA01.SUBSCRIBER_LIST " + "WHERE COMPONENT_ID = ? ";
	private static String SELECT_FREE_COUNTER_GROUP_ID =
		"SELECT MAX (COUNTER_GROUP_ID) + 1 as GROUP_ID FROM KOA01.COUNTERS ";
	private static String INSERT_COUNTER_DATA =
		"INSERT INTO KOA01.COUNTERS "
			+ "(COMPONENT_ID, COUNTER_GROUP_ID, COUNTER_ID, COMPONENT_TYPE, ACTION, TIMESTAMP, COUNTER_VALUE) VALUES (?, ?, ?, ?, ?, ?, ?) ";
	private static String INSERT_PUBLIC_KEY =
		"UPDATE KOA01.KOA_INTERNAL SET PUBLIC_KEY = (?)";
	private static String SELECT_PUBLIC_KEY =
		"SELECT PUBLIC_KEY as PUBLIC_KEY FROM KOA01.KOA_INTERNAL ";
	private static String SELECT_SUBSCRIBERS =
		"SELECT 	COMPONENT_ID as COMPONENT_ID, "
			+ "			JNDI_NAME as JNDI_NAME, "
			+ " 			COMPONENT_TYPE as COMPONENT_TYPE, "
			+ " 			CONTEXT as CONTEXT, "
			+ " 			CONTEXT_FACTORY as CONTEXT_FACTORY "
			+ "FROM KOA01.SUBSCRIBER_LIST ";
	private static String SELECT_PINCODE =
		"SELECT PIN_ID	"
			+ "FROM 	KOA01.PINCODE "
			+ "WHERE 	PIN_ID = ? ";
	/**
	 * Get the most current counters from the database
	 * Returning an vector filled with CounterData objects
	 * for every component type the counters cumulated.
	 * 
	 * @return Vector containing the most recent counters for all the component types
	 * 
	 * @throws KOAException exception when something goes wrong
	 * 
	 */
	public Vector getCurrentCounters() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getCurrentCounters] start get current counters");
		/* init variables */
		Vector vCounters = new Vector();
		CounterData xCounterData = null;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the query */
			rsResult =
				xDBUtils.executeResultQuery(
					stmtStatement,
					SELECT_CURRENT_COUNTERS);
			String sComponentType = null;
			while (rsResult != null && rsResult.next())
			{
				String sCurrentComponent = rsResult.getString("COMPONENT_TYPE");
				String sCounterKey = rsResult.getString("COUNTER_ID");
				long lCounterValue = rsResult.getLong("COUNTER_VALUE");
				Timestamp tsTimestamp = rsResult.getTimestamp("TIMESTAMP");
				/* check if it is a new component type */
				if (sComponentType == null
					|| !sComponentType.equals(sCurrentComponent))
				{
					/* create new instance and add instance to vector */
					sComponentType = sCurrentComponent;
					xCounterData =
						new CounterData(sComponentType, sComponentType);
					/* Adding date/time to the counterdata */
					xCounterData.setTimestamp(tsTimestamp);
					vCounters.add(xCounterData);
				}
				/* set the counter key and value  */
				xCounterData.setCounter(sCounterKey, lCounterValue);
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.getCurrentCounters",
				"error getting current counters",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Select current counters" };
			KOALogHelper.logErrorCode(
				"ControllerDB.getCurrentCounters",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_GET_COUNTERS,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* return the set of counters */
		return vCounters;
	}
	/**
	 * Get the counter value for a counter
	 * 
	 * @param  sCounterKey  the counter for which the value is returned.
	 * @return long the counter value
	 * 
	 * @throws KOAException Execption when something goes wrong during fetching
	 */
	public long getCurrentWebCounter(String sCounterKey) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getCurrentWebCounter] start get current counter");
		long lCounterValue = 0;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		ResultSet rsResult = null;
		try
		{
			/* get connection */
			conn = xDBUtils.getConnection();
			/* setup the prepared statement */
			xPre = conn.prepareStatement(SELECT_CURRENT_WEB_COUNTER);
			xPre.setString(1, sCounterKey.toUpperCase());
			/* execute the statement */
			rsResult = xPre.executeQuery();
			/* get the result */
			if (rsResult != null && rsResult.next())
			{
				/* getting counter value */
				lCounterValue = rsResult.getLong("COUNTER_VALUE");
			}
			else
			{
				lCounterValue = 0;
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.getCurrentWebCounter",
				"Problems getting counter value",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Get web counter value" };
			KOALogHelper.logErrorCode(
				"ControllerDB.getCurrentWebCounter",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_GET_WEB_COUNTER,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getCurrentWebCounter] returning counter value "
				+ lCounterValue);
		/* return the value of the counter */
		return lCounterValue;
	}
	/**
	 * Gets the first free counter data group id that is
	 * not in use.
	 * 
	 * @return int the free counter group id
	 * 
	 * @throws KOAException Execption when something goes wrong
	 * 
	 */
	public int getCounterGroupID() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getCounterGroupID] start get free counter group id");
		/* init variables */
		int iFreeID = 0;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the select query */
			rsResult =
				xDBUtils.executeResultQuery(
					stmtStatement,
					SELECT_FREE_COUNTER_GROUP_ID);
			/* get the result */
			if (rsResult != null && rsResult.next())
			{
				/* getting free ID */
				iFreeID = rsResult.getInt("GROUP_ID");
			}
			else
			{
				iFreeID = 1;
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.getCounterGroupID",
				"Problems getting free id",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Get free counter group id" };
			KOALogHelper.logErrorCode(
				"ControllerDB.getCounterGroupID",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(
				ErrorConstants.CONTROLLER_DB_GET_GROUP_ID,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getCounterGroupID] returning group id " + iFreeID);
		/* return the set of counters */
		return iFreeID;
	}
	/**
	 * Insert the counter data into the database
	 * 
	 * @param iCounterGroupID The counter group id to use. This identifies all the counters that belong to the same collection process.
	 * @param sAction The action that has initiated the collection of the counters.
	 * @param xCounterData The data to save
	 * 
	 * @throws KOAException Exception when something goes wrong during insert
	 * 
	 */
	public void insertCounterData(
		int iCounterGroupID,
		Timestamp tsTimestamp,
		String sAction,
		CounterData xCounterData)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.insertCounterData] start inserting counter data in DB");
		if (xCounterData == null)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ControllerDB.insertCounterData] counter data object is empty, could not set counter data in db");
			return;
		}
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			/* get all the keys from the counter data object */
			Enumeration enum = xCounterData.getCounterKeys();
			String sCounterKey = null;
			while (enum.hasMoreElements())
			{
				sCounterKey = (String) enum.nextElement();
				try
				{
					/* setup the prepared statement */
					xPre = conn.prepareStatement(INSERT_COUNTER_DATA);
					xPre.setString(1, xCounterData.getComponentID());
					xPre.setInt(2, iCounterGroupID);
					xPre.setString(3, sCounterKey);
					xPre.setString(4, xCounterData.getComponentType());
					xPre.setString(5, sAction);
					xPre.setTimestamp(6, tsTimestamp);
					xPre.setLong(7, xCounterData.getCounter(sCounterKey));
					/* execute the statement */
					xPre.executeUpdate();
				}
				finally
				{
					/* close prepared statement */
					xDBUtils.closePreparedStatement(xPre);
				}
			}
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Insert counter data" };
			KOALogHelper.logErrorCode(
				"ControllerDB.insertCounterData",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_INSERT_COUNTERS,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeConnection(conn);
		}
	}
	/**
	 * Gets the first free unique number from the database.
	 * It also adds one to the counter to make sure the
	 * ID is unique for the next caller.
	 * 
	 * @return int the free id
	 * 
	 */
	public int getFreeID() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getFreeID] start get free id");
		/* init variables */
		int iFreeID = 0;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* check if there is a row */
			if (this.koaInternalHasRow(conn))
			{
				/* execute the select query */
				rsResult =
					xDBUtils.executeResultQuery(stmtStatement, SELECT_FREE_ID);
				/* loop through the result */
				while (rsResult != null && rsResult.next())
				{
					/* getting free ID */
					iFreeID = rsResult.getInt("FREE_ID");
				}
				/* if we have a free ID, update the free id */
				int iNrRecordsAffected = xDBUtils.executeQuery(UPDATE_FREE_ID);
				if (iNrRecordsAffected == 0)
				{
					KOALogHelper.log(
						KOALogHelper.WARNING,
						"[ControllerDB.getFreeID] free id not updated");
				}
			}
			else
			{
				int iNrRecordsAffected =
					xDBUtils.executeQuery(INSERT_KOA_INTERNAL_RECORD);
				if (iNrRecordsAffected == 0)
				{
					KOALogHelper.log(
						KOALogHelper.WARNING,
						"[ControllerDB.getFreeID] koa internal row not inserted");
				}
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.getFreeID",
				"Problems getting free id",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Get free unique ID" };
			KOALogHelper.logErrorCode(
				"ControllerDB.getFreeID",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_GET_FREE_ID,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* return the set of counters */
		return iFreeID;
	}
	/**
	 * Checks if the KOA_INTERNAL database table 
	 * has a record.
	 * 
	 * @param conn the connection to the database
	 * 
	 * @return boolean indicating if there is a record (true) or there is no record (false)
	 * 
	 * @throws KOAException exception when something goes wrong.
	 * 
	 */
	private boolean koaInternalHasRow(Connection conn) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.koaInternalHasRow] check if internal table has row");
		/* init the variables */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		boolean bResult = false;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* loop through the result */
		try
		{
			/* get statement */
			stmtStatement = conn.createStatement();
			/* execute the query */
			rsResult =
				xDBUtils.executeResultQuery(
					stmtStatement,
					SELECT_KOA_INTERNAL_ROWCOUNT);
			while (rsResult != null && rsResult.next())
			{
				/* check the number of rows */
				bResult = rsResult.getInt("COUNT") != 0;
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.koaInternalHasRow",
				"error checking if the internal table has a row",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Check if internal row exists" };
			KOALogHelper.logErrorCode(
				"ControllerDB.koaInternalHasRow",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_CHECK_INTERNAL_ROW,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
		}
		/* return the boolean */
		return bResult;
	}
	/**
	 * Add the client subscription to the database. This method
	 * is used by the controller to store the subscription in the database.
	 * 
	 * @param xSubScription The subscription to add to the database
	 * 
	 * @throws KOAException exception when something goes wrong in the communication with the database 
	 * 
	 */
	public void addSubscription(ClientSubscription xSubScription)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.addSubscription] start adding subscription to db");
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			/* setup the prepared statement */
			xPre = conn.prepareStatement(INSERT_CLIENT_SUBSCRIPTION);
			xPre.setString(1, xSubScription.getComponentID());
			xPre.setString(2, xSubScription.getJNDIName());
			xPre.setString(3, xSubScription.getComponentType());
			xPre.setString(4, xSubScription.getContext());
			xPre.setString(5, xSubScription.getContextFactory());
			/* execute the statement */
			xPre.executeUpdate();
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Insert Client Subscription" };
			KOALogHelper.logErrorCode(
				"ControllerDB.addSubscription",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_SUBSCRIBE,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
	}
	/**
	 * Remove the client subscription from the db. This method
	 * is used by the controller to delete the subscription in the database.
	 * 
	 * @param sComponentID The componentID to add to the database
	 * 
	 * @throws KOAException exception when something goes wrong in the communication with the database 
	 * 
	 */
	public void removeSubscription(String sComponentID) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.removeSubscription] start removing subscription with ID "
				+ sComponentID);
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			/* setup the prepared statement */
			xPre = conn.prepareStatement(DELETE_CLIENT_SUBSCRIPTION);
			xPre.setString(1, sComponentID);
			/* execute the statement */
			xPre.executeUpdate();
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Remove Client Subscription" };
			KOALogHelper.logErrorCode(
				"ControllerDB.removeSubscription",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_UNSUBSCRIBE,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
	}
	/**
	 * Gets the number of subscribers for registered in the database
	 * 
	 * @param conn the connection to the database
	 * 
	 * @return boolean indicating if there is a record (true) or there is no record (false)
	 * 
	 * @throws KOAException exception when something goes wrong
	 * 
	 */
	public int getNumberOfSubscribers() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getNumberOfSubscribers] get the number of subscribers in the database");
		/* init the variables */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		int iResult = 0;
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
				xDBUtils.executeResultQuery(
					stmtStatement,
					SELECT_SUBSCRIBER_LIST_ROWCOUNT);
			while (rsResult != null && rsResult.next())
			{
				/* check the number of rows */
				iResult = rsResult.getInt("COUNT");
			}
		}
		/* catch all KOA exceptions */
		catch (KOADBException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.getNumberOfSubscribers",
				"Error during get the number of subscribers in the database",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Select number of subscriptions" };
			KOALogHelper.logErrorCode(
				"ControllerDB.getNumberOfSubscribers",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_COUNT_SUBSCRIBERS,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* return the row count */
		return iResult;
	}
	/**
	 * Get the subscribers from the database
	 * Returning an vector filled with ClientSubscription objects
	 * 
	 * @return Vector containing the most recent counters for all the component types
	 * 
	 * @throws KOAException exception if something goes wrong
	 * 
	 */
	public Vector getSubscribers() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.getCurrentCounters] start get current counters");
		/* init variables */
		Vector vSubscriptions = new Vector();
		ClientSubscription xClientSubscription = null;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the query */
			rsResult =
				xDBUtils.executeResultQuery(stmtStatement, SELECT_SUBSCRIBERS);
			String sComponentID = null;
			String sJNDIName = null;
			String sComponentType = null;
			String sContext = null;
			String sContextFactory = null;
			while (rsResult != null && rsResult.next())
			{
				/* get all the variables from the result set */
				sComponentID = rsResult.getString("COMPONENT_ID");
				sJNDIName = rsResult.getString("JNDI_NAME");
				sComponentType = rsResult.getString("COMPONENT_TYPE");
				sContext = rsResult.getString("CONTEXT");
				sContextFactory = rsResult.getString("CONTEXT_FACTORY");
				/* check if it is an ESB module */
				if (sComponentType.equals(ComponentType.ESB))
				{
					/* create new ESB subscription */
					xClientSubscription =
						new ESBClientSubscription(
							sComponentID,
							sJNDIName,
							sContext,
							sContextFactory);
				}
				/* check if it is an KR module */
				else if (sComponentType.equals(ComponentType.KR))
				{
					/* create new KR subscription */
					xClientSubscription =
						new KRClientSubscription(
							sComponentID,
							sJNDIName,
							sContext,
							sContextFactory);
				}
				/* if it isn't an ESB or a KR, it is a WEB/TSM/Stemproces */
				else
				{
					/* create new control client subscription for WEB/TSM/Stemproces */
					xClientSubscription =
						new ControlClientSubscription(
							sComponentType,
							sJNDIName,
							sContext,
							sContextFactory);
				}
				/* add the subscription to the vector */
				vSubscriptions.add(xClientSubscription);
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.getCurrentCounters",
				"error getting current counters",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Select current counters" };
			KOALogHelper.logErrorCode(
				"ControllerDB.getCurrentCounters",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_GET_SUBSCRIBERS,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* return the set of counters */
		return vSubscriptions;
	}
	/**
	 * Loads the public key from the database
	 * 
	 * @return PublicKey the public key of the KOA system
	 * 
	 * @throws KOAException when something goes wrong while getting the public key from the db
	 * 
	 */
	public PublicKey loadPublicKey() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.loadPublicKey] start load the public key");
		/* init variables */
		PublicKey pkPublicKey = null;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* loop through the result */
		try
		{
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the query */
			rsResult =
				xDBUtils.executeResultQuery(stmtStatement, SELECT_PUBLIC_KEY);
			while (rsResult != null && rsResult.next())
			{
				/* get all the variables from the result set */
				byte[] baBytes = rsResult.getBytes("PUBLIC_KEY");
				/* convert the byte array to the public key */
				Convertor xConvertor = new Convertor();
				pkPublicKey = xConvertor.byteArrayToPublicKey(baBytes);
			}
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Load public key" };
			KOALogHelper.logErrorCode(
				"ControllerDB.loadPublicKey",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_LOAD_PUBLICKEY,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		/* throw koa exception if no public key is obtained from db */
		if (pkPublicKey == null)
		{
			KOALogHelper.logError(
				"ControllerDB.loadPublicKey",
				"Public key is null... Can not load public key from db",
				null);
			throw new KOAException(ErrorConstants.CONTROLLER_DB_LOAD_PUBLICKEY);
		}
		/* return the public key */
		return pkPublicKey;
	}
	/**
	 * Saves the public key of the KOA system to the database
	 * 
	 * @param pkPublicKey the public key
	 * 
	 * @throws KOAException when something goes wrong while saving the public key to the db
	 * 
	 */
	public void savePublicKey(PublicKey pkPublicKey) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.savePublicKey] start save public key ");
		/* throw koa exception if no public key is specified */
		if (pkPublicKey == null)
		{
			KOALogHelper.logError(
				"ControllerDB.savePublicKey",
				"Public key is null... Can not save public key",
				null);
			throw new KOAException(ErrorConstants.CONTROLLER_DB_SAVE_PUBLICKEY);
		}
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		try
		{
			/* get the connection */
			conn = xDBUtils.getConnection();
			if (!this.koaInternalHasRow(conn))
			{
				int iNrRecordsAffected =
					xDBUtils.executeQuery(INSERT_KOA_INTERNAL_RECORD);
				if (iNrRecordsAffected == 0)
				{
					KOALogHelper.logError(
						"ControllerDB.savePublicKey",
						"koa internal row not inserted",
						null);
				}
			}
			/* convert the public key to a byte array */
			Convertor xConvertor = new Convertor();
			byte[] baBytes = xConvertor.publicKeyToByteArray(pkPublicKey);
			/* setup the prepared statement */
			xPre = conn.prepareStatement(INSERT_PUBLIC_KEY);
			xPre.setBytes(1, baBytes);
			/* execute the statement */
			xPre.executeUpdate();
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Insert public key" };
			KOALogHelper.logErrorCode(
				"ControllerDB.savePublicKey",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_SAVE_PUBLICKEY,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
	}
	/**
	 * checks if there are any records in the candidate list.
	 * 
	 * @return boolean indicating if there are any candidates (true) or not (false)
	 * 
	 */
	public boolean systemContainsCandidates()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.systemContainsCandidates] start checking if there are candidates in the system");
		/* init variables */
		boolean bContainsCanidates = false;
		Connection conn = null;
		Statement stmtStatement = null;
		ResultSet rsResult = null;
		DBUtils xDBUtils = null;
		/* loop through the result */
		try
		{
			/* init the DBUtils class */
			xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			/* get connection and statement */
			conn = xDBUtils.getConnection();
			stmtStatement = conn.createStatement();
			/* execute the select query */
			rsResult =
				xDBUtils.executeResultQuery(
					stmtStatement,
					SELECT_COUNT_CANDIDATES);
			/* get the result */
			if (rsResult != null && rsResult.next())
			{
				int iNrOfRows = rsResult.getInt("COUNT");
				if (iNrOfRows > 0)
				{
					bContainsCanidates = true;
				}
				else
				{
					bContainsCanidates = false;
				}
			}
			else
			{
				bContainsCanidates = false;
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.systemContainsCandidates",
				"Problems getting free id",
				koae);
			bContainsCanidates = false;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Check if system contains candidates" };
			KOALogHelper.logErrorCode(
				"ControllerDB.systemContainsCandidates",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			bContainsCanidates = false;
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closeStatement(stmtStatement);
			xDBUtils.closeConnection(conn);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.systemContainsCandidates] result, system contains candidates: "
				+ bContainsCanidates);
		/* return the set of counters */
		return bContainsCanidates;
	}
	/**
	 * OR 22.3.602 Gebruik pincode voor statuswijziging
	 * Check if the pincodes exist
	 * 
	 * @param  sPincode1  the first pincode to be checked.
	 * @param  sPincode2  the second pincode to be checked.
	 * @return boolean    the result of the check
	 * 
	 * @throws KOAException Execption when something goes wrong during fetching
	 * 
	 */
	public boolean checkPinCode(String sPincode1, String sPincode2)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.checkPinCode] start checking pincodes...");
		boolean bCheckPin = false;
		/* init the DBUtils class */
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		/* execute the query */
		Connection conn = null;
		PreparedStatement xPre = null;
		ResultSet rsResult = null;
		try
		{
			/* get connection */
			conn = xDBUtils.getConnection();
			/* setup the prepared statement voor sPincode1 */
			xPre = conn.prepareStatement(SELECT_PINCODE);
			xPre.setString(1, sPincode1);
			/* execute the statement */
			rsResult = xPre.executeQuery();
			/* get the result */
			if (rsResult != null && rsResult.next())
			{
				/* getting counter value */
				bCheckPin = true;
			}
			else
			{
				return false;
			}
			/* setup the preparedstatement voor sPincode2 */
			xPre.setString(1, sPincode2);
			/* execute the statement */
			rsResult = xPre.executeQuery();
			/* get the result */
			if (rsResult != null && rsResult.next())
			{
				/* getting counter value */
				bCheckPin = true;
			}
			else
			{
				return false;
			}
		}
		/* catch all KOA exceptions */
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ControllerDB.checkPinCode",
				"Problems getting pincode",
				koae);
			throw koae;
		}
		/* catch all the errors concerning SQL */
		catch (SQLException sqle)
		{
			String[] params = { "Get pincode" };
			KOALogHelper.logErrorCode(
				"ControllerDB.checkPinCode",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADBException(
				ErrorConstants.CONTROLLER_DB_GET_PINCODE,
				sqle);
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rsResult);
			xDBUtils.closePreparedStatement(xPre);
			xDBUtils.closeConnection(conn);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ControllerDB.checkPinCode] pincode exists:" + bCheckPin);
		/* return the value of the counter */
		return bCheckPin;
	}
}