/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.controller.client.SOAPControlClient.java
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
  *  0.1		11-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.controller.client;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Enumeration;

import com.logicacmg.koa.adapter.soap.TSMSOAPAdapter;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.client.AbstractControlClient;
import com.logicacmg.koa.controller.client.ControlClient;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The SOAP implementation of the control client.
 * This control client implementation is used for the 
 * SOAP-communication with a SOAP adapter.
 * 
 * @author KuijerM
 * 
 */
public class SOAPControlClient
	extends AbstractControlClient
	implements ControlClient
{
	private String g_sIPAddress = null;
	private String g_sIdentifier = null;
	private CounterData g_LatestCounterData = null;
	/**
	 * Constructor for the SOAP implementation of the 
	 * control client
	 * 
	 * @param sComponentType The identifier of the component type
	 * 
	 * @throws Exception General Exceptions
	 * 
	 */
	public SOAPControlClient(
		String sComponentType,
		String sIPAddress,
		String sIdentifier)
		throws Exception
	{
		/* call super constructor to set the componenttype */
		super(sComponentType);
		/* set the identifier of the soap client */
		this.g_sIdentifier = sIdentifier;
		this.g_sIPAddress = sIPAddress;
	}
	/**
	 * Remote method to notify the control client that the  
	 * state has changed.
	 * 
	 * @param sNewState The new state
	 * 
	 * @return The boolean indicating if the update of the state was succesful
	 * 
	 * @throws RemoteException RMI Exception
	 * 
	 */
	public boolean notifyState(String sNewState) throws RemoteException
	{
		boolean returnValue;
		String prevState = null;
		prevState = g_sCurrentState;
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SOAPControlClient.notify]  Component "
				+ g_sComponentType
				+ ", Controller notified new State "
				+ sNewState);
		/* set the state */
		super.g_sCurrentState = sNewState;
		/* create a new SOAP adapter */
		TSMSOAPAdapter xAdapter =
			new TSMSOAPAdapter(g_sJNDIName, g_sIPAddress, g_sIdentifier);
		/* If the newstate will be reinititialized or initialized
		   store the counter data */
		try
		{
			if (sNewState.equals(SystemState.RE_INITIALIZED)
				|| sNewState.equals(SystemState.INITIALIZED))
			{
				storeCounterData(xAdapter.collectCounterData());
			}
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SOAPControlClient.notifyState",
				"Could not store counter data",
				koae);
			return false;
		}
		/* notify the state to the TSM */
		returnValue = xAdapter.notifyState(sNewState);
		g_LatestCounterData = xAdapter.getLatestCounterData();
		return returnValue;
	}
	/**
	 * Remote method to collect all the counters available 
	 * on this client
	 * 
	 * @return The counter data object with all the counters
	 * 
	 * @throws RemoteException RMI Exception
	 * 
	 */
	public CounterData collectCounters(int reason) throws RemoteException
	{
		/* We have a look at the reason to determine if we
		   should really perform a getStatistics on the TSM */
		CounterData cData = null;
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SOAPControlClient.collectCounters] Component "
				+ g_sComponentType
				+ ", Collecting counter data");
		/* create a new SOAP adapter */
		TSMSOAPAdapter xAdapter =
			new TSMSOAPAdapter(g_sJNDIName, g_sIPAddress, g_sIdentifier);
		if (reason != CounterKeys.STATECHANGE)
		{
			/* Explicitly collect the counters from the TSM */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.collectCounters] Component "
					+ g_sComponentType
					+ ", Collect counters requested by SCHEDULER");
			cData = xAdapter.collectCounterData();
		}
		else
		{
			/* Already retrieved the counterdata with the statechange */
			/* Did we store it? */
			if (!super.g_sCurrentState.equals(SystemState.INITIALIZED)
				&& !super.g_sCurrentState.equals(SystemState.RE_INITIALIZED))
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[SOAPControlClient.collectCounters] Component "
						+ g_sComponentType
						+ ", Using counterdata from STATECHANGE");
				cData = g_LatestCounterData;
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[SOAPControlClient.collectCounters] Component "
						+ g_sComponentType
						+ ", Counterdata should be in DB so create EMPTY object");
				cData = new CounterData(ComponentType.TEL, g_sJNDIName);
			}
		}
		/* return if result is null */
		if (cData == null)
		{
			return null;
		}
		/* Retrieve the summed counters from the database and add them to this cdata */
		DBUtils xDbKoa;
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		String query;
		String key = null;
		long accValue;
		long value;
		try
		{
			xDbKoa =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.collectCounter] Get connection");
			conn = xDbKoa.getConnection();
			/* Get max group_id */
			stmt = conn.createStatement();
			query =
				"select COUNTER_ID, sum(value) as VALUE from koa01.tsmcount where component_id='"
					+ g_sIPAddress
					+ "' group by counter_id";
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.collectCounters] Got resultset");
			rst = stmt.executeQuery(query);
			/* Loop through the resultset and increment the cdata values */
			while (rst.next())
			{
				key = rst.getString("COUNTER_ID");
				value = rst.getBigDecimal("VALUE").longValue();
				accValue = cData.getCounter(key);
				if (accValue == -1)
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[SOAPControlClient.collectCounters] KEY: "
							+ key
							+ ", setting: "
							+ value);
					cData.setCounter(key, value);
				}
				else
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[SOAPControlClient.collectCounters] KEY: "
							+ key
							+ ", adding: "
							+ value
							+ " + "
							+ accValue);
					cData.setCounter(key, value + accValue);
				}
			}
			rst.close();
			stmt.close();
			conn.commit();
			conn.close();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.collectCounters] Finished computing counters for TSM");
		}
		catch (SQLException sqle)
		{
			String[] params =
				{ "Collection of TSM counters in temp table for counters" };
			KOALogHelper.logErrorCode(
				"SOAPControlClient",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SOAPControlClient",
				"KOAException, are the JNDI properties valid?",
				koae);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"SOAPControlClient.storeCounterData",
				ErrorConstants.ERR_CONTROL_CLIENT_DEFAULT,
				e);
		}
		finally
		{
			try
			{
				conn.close();
			}
			catch (Exception e)
			{
			}
		}
		return cData;
	}
	/**
	 * Method to write the counter values to the database
	 * 
	 * @param type indicator: scheduled or which statechange
	 * @param data counterdata to insert
	 * 
	 */
	private void storeCounterData(CounterData data) throws KOAException
	{
		if (data == null)
		{
			throw new KOAException();
		}
		DBUtils xDbKoa;
		Connection conn = null;
		String key;
		String query;
		Statement stmt;
		int nextGroup;
		try
		{
			xDbKoa =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.storeCounterData] Get connection");
			conn = xDbKoa.getConnection();
			/* Get max group_id */
			stmt = conn.createStatement();
			query = "SELECT MAX(GROUP_ID) AS MAX FROM KOA01.TSMCOUNT";
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.storeCounterData] Get max group id");
			ResultSet rst = stmt.executeQuery(query);
			if (rst.next())
			{
				BigDecimal dec = rst.getBigDecimal("MAX");
				if (dec != null)
				{
					nextGroup = dec.intValue() + 1;
				}
				else
				{
					nextGroup = 1;
				}
			}
			else
			{
				nextGroup = 1;
			}
			rst.close();
			stmt.close();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SOAPControlClient.storeCounterData] nextGroup: " + nextGroup);
			// Loop through the counters and insert them into the database */
			Enumeration enum = data.getCounterKeys();
			while (enum.hasMoreElements())
			{
				key = (String) enum.nextElement();
				if ((key != null) && (key.length() != 0))
				{
					stmt = conn.createStatement();
					query =
						"INSERT INTO KOA01.TSMCOUNT(GROUP_ID, COMPONENT_ID, COUNTER_ID, VALUE) VALUES ("
							+ nextGroup
							+ ",'"
							+ g_sIPAddress
							+ "','"
							+ key
							+ "',"
							+ data.getCounter(key)
							+ ")";
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[SOAPControlClient.storeCounterData] query: " + query);
					stmt.executeUpdate(query);
					stmt.close();
				}
			}
			conn.commit();
			conn.close();
		}
		catch (SQLException sqle)
		{
			String[] params =
				{ "Inserting the TSM counters in the temp table" };
			KOALogHelper.logErrorCode(
				"SOAPControlClient",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SOAPControlClient",
				"KOAException, are the JNDI properties valid?",
				koae);
			throw koae;
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"SOAPControlClient.storeCounterData",
				ErrorConstants.ERR_CONTROL_CLIENT_DEFAULT,
				e);
			throw new KOAException();
		}
		finally
		{
			try
			{
				conn.close();
			}
			catch (Exception e)
			{
			}
		}
	}
	/**
	 * Method to update counter. 
	 * For the SOAP interface this is not used.
	 * 
	 * @param sCounterKey the key to update
	 * 
	 */
	public synchronized void updateCounter(String sCounterKey)
	{
		//do nothing
	}
	/**
	 * Method to initialize counter. 
	 * For the SOAP interface this is not used.
	 * 
	 * @param sCounterKey the key to update
	 * 
	 */
	public synchronized void initializeCounter(String sCounterKey)
	{
		//do nothing
	}
}