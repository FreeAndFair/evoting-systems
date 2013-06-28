/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.CounterData.java
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
  *  0.1		11-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.io.Serializable;
import java.sql.Timestamp;
import java.util.Enumeration;
import java.util.Hashtable;

import com.logicacmg.koa.db.ControllerDB;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Dataobject to collect all the counters that are
 * managed on a number of components
 * 
 * @author KuijerM
 * 
 */
public class CounterData implements Serializable
{
	/* component type identifier */
	private String g_sComponentType;
	/* id of the component */
	private String g_sComponentID;
	/* hashtable containing all the counter with values */
	private Hashtable g_mCounters;
	private Timestamp g_tsTimestamp = null;
	/**
	 * The contructor for the counter data
	 * 
	 * @param sComponentType The component type identifier.
	 * @param sComponentID The unique identifier of the component
	 * 
	 */
	public CounterData(String sComponentType, String sComponentID)
	{
		g_sComponentType = sComponentType;
		g_sComponentID = sComponentID;
		this.resetCounters();
	}
	/**
	 * Gets the component type for this counter data object.
	 * 
	 * @return String the component type identifier
	 * 
	 */
	public String getComponentType()
	{
		return this.g_sComponentType;
	}
	/**
	 * Gets the component id
	 * 
	 * @return String component ID
	 * 
	 */
	public String getComponentID()
	{
		return this.g_sComponentID;
	}
	/**
	 * returns the value for the specified counter key
	 * 
	 * @param sCounterKey The identifier for the counter
	 * 
	 * @return value for the specified counter key, if the counter is not known, -1 is returned.
	 * 
	 */
	public long getCounter(String sCounterKey)
	{
		long lValue = -1;
		if (this.containsKey(sCounterKey))
		{
			Long lTemp = (Long) g_mCounters.get(sCounterKey);
			lValue = lTemp.longValue();
		}
		return lValue;
	}
	/**
	 * add 1 for the counter specified in the parameter
	 * 
	 * @param sCounterKey the counter key identifier
	 * 
	 */
	public void updateCounter(String sCounterKey)
	{
		// check if the counter exists 
		if (this.containsKey(sCounterKey))
		{
			// if the counter exists read the value 
			Long lTemp = (Long) g_mCounters.get(sCounterKey);
			long lValue = lTemp.longValue();
			// add 1 to the value 
			lValue++;
			// put back the value in the hashtable under the right key 
			g_mCounters.put(sCounterKey, new Long(lValue));
		}
		else
		{
			// create new counter key with value 1 
			g_mCounters.put(sCounterKey, new Long(1));
		}
	}
	/**
	 * Get the initial counter value from the database if the counter doesn't exist.
	 * if the counter already exists, nothing is done.
	 * 
	 * @param sCounterKey the counter key identifier
	 * 
	 */
	public void initializeCounter(String sCounterKey)
	{
		/* check if the counter exists */
		if (!this.containsKey(sCounterKey))
		{
			// Initialize counter with the value from the database
			long lCounterValue = 0;
			ControllerDB xControllerDB = new ControllerDB();
			try
			{
				lCounterValue = xControllerDB.getCurrentWebCounter(sCounterKey);
			}
			catch (KOAException koae)
			{
				KOALogHelper.logError(
					"CounterData.initializeCounter",
					"Problem getting counter from database",
					koae);
			}
			if (lCounterValue == 0)
			{
				/* create new counter key with value 0 */
				g_mCounters.put(sCounterKey, new Long(0));
			}
			else
			{
				g_mCounters.put(sCounterKey, new Long(lCounterValue));
			}
		}
	}
	public void setCounter(String sCounterKey, long lCounterValue)
	{
		/* set the counter value */
		g_mCounters.put(sCounterKey, new Long(lCounterValue));
	}
	/**
	 * Reset all the counters by creating a new hashtable
	 * 
	 */
	public void resetCounters()
	{
		/* if it is null, init new hashtable */
		if (g_mCounters == null)
		{
			g_mCounters = new Hashtable();
		}
		/* get all the counters */
		Enumeration enum = this.getCounterKeys();
		/* reset all the knwown counters */
		String key = null;
		while (enum.hasMoreElements())
		{
			key = (String) enum.nextElement();
			g_mCounters.put(key, new Long(0));
		}
	}
	/**
	 * Gets all the counter keys that are available in this
	 * counter data object.
	 * 
	 * @return Enumeration containing all the keys
	 * 
	 */
	public Enumeration getCounterKeys()
	{
		if (g_mCounters != null)
		{
			return g_mCounters.keys();
		}
		else
		{
			return new Hashtable().keys();
		}
	}
	/**
	 * checks if the key already is in the hashtable
	 * 
	 * @param sCounterKey the counter key identifier.
	 *
	 * @return boolean indicating if the counter is in the table (true) or not (false)
	 *  
	 */
	private boolean containsKey(String sCounterKey)
	{
		/* check if the key is in the hashtable */
		return g_mCounters != null
			&& !g_mCounters.isEmpty()
			&& g_mCounters.containsKey(sCounterKey);
	}
	/**
	 * Set the timestamp of this counter data values object
	 * 
	 * @param tsTimestamp The timestamp of the values of this data object
	 * 
	 */
	public void setTimestamp(Timestamp tsTimestamp)
	{
		this.g_tsTimestamp = tsTimestamp;
	}
	/**
	 * Gets the timestamp of this counter data values object
	 * 
	 * @return Timestamp The timestamp of this object.
	 * 
	 */
	public Timestamp getTimestamp()
	{
		return this.g_tsTimestamp;
	}
}