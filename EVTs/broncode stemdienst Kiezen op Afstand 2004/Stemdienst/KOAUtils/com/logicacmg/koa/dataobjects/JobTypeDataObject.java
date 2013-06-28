/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.JobTypeDataObject.java
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
  *  0.1		28-04-2003	MKu	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.math.BigDecimal;
import java.sql.Timestamp;
/**
 * DataObject for Job type data.
 * @author JvG
 */
public class JobTypeDataObject implements java.io.Serializable
{
	// PK
	private BigDecimal jobTypeID = null;
	private String name = null;
	private int priority = -1;
	private Timestamp firstTime = null;
	private BigDecimal successor = null;
	private BigDecimal interval = null;
	public JobTypeDataObject()
	{
	}
	public JobTypeDataObject(BigDecimal id)
	{
		this.jobTypeID = id;
	}
	/**
	 * Gets the firstTime
	 * @return Returns a Timestamp
	 */
	public Timestamp getFirstTime()
	{
		return firstTime;
	}
	/**
	 * Sets the firstTime
	 * @param firstTime The firstTime to set
	 */
	public void setFirstTime(Timestamp firstTime)
	{
		this.firstTime = firstTime;
	}
	/**
	 * Gets the interval
	 * @return Returns a BigDecimal
	 */
	public BigDecimal getInterval()
	{
		return interval;
	}
	/**
	 * Sets the interval
	 * @param interval The interval to set
	 */
	public void setInterval(BigDecimal interval)
	{
		this.interval = interval;
	}
	/**
	 * Gets the jobTypeID
	 * @return Returns a BigDecimal
	 */
	public BigDecimal getJobTypeID()
	{
		return jobTypeID;
	}
	/**
	 * Sets the jobTypeID
	 * @param jobTypeID The jobTypeID to set
	 */
	public void setJobTypeID(BigDecimal jobTypeID)
	{
		this.jobTypeID = jobTypeID;
	}
	/**
	 * Gets the name
	 * @return Returns a String
	 */
	public String getName()
	{
		return name;
	}
	/**
	 * Sets the name
	 * @param name The name to set
	 */
	public void setName(String name)
	{
		this.name = name;
	}
	/**
	 * Gets the priortity
	 * @return Returns a int
	 */
	public int getPriority()
	{
		return priority;
	}
	/**
	 * Sets the priortity
	 * @param priortity The priortity to set
	 */
	public void setPriority(int priority)
	{
		this.priority = priority;
	}
	/**
	 * Gets the successor
	 * @return Returns a BigDecimal
	 */
	public BigDecimal getSuccessor()
	{
		return successor;
	}
	/**
	 * Sets the successor
	 * @param successor The successor to set
	 */
	public void setSuccessor(BigDecimal successor)
	{
		this.successor = successor;
	}
}
