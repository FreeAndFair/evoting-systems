/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.ScheduledJobDataObject.java
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
 * DataObject for subsription data.
 * @author JvG
 */
public class ScheduledJobDataObject implements java.io.Serializable
{
	// PK
	private BigDecimal jobID = null;
	private BigDecimal jobType = null;
	private Timestamp startTime = null, stopTime = null;
	private int priority = -1;
	private String status = null, message = null, jobTypeName = null;
	public ScheduledJobDataObject()
	{
	}
	public ScheduledJobDataObject(BigDecimal id)
	{
		this.jobID = id;
	}
	/**
	 * Gets the jobID
	 * @return Returns a BigDecimal
	 */
	public BigDecimal getJobID()
	{
		return jobID;
	}
	/**
	 * Sets the jobID
	 * @param jobID The jobID to set
	 */
	public void setJobID(BigDecimal jobID)
	{
		this.jobID = jobID;
	}
	/**
	 * Gets the jobType
	 * @return Returns a BigDecimal
	 */
	public BigDecimal getJobType()
	{
		return jobType;
	}
	/**
	 * Sets the jobType
	 * @param jobType The jobType to set
	 */
	public void setJobType(BigDecimal jobType)
	{
		this.jobType = jobType;
	}
	/**
	 * Gets the startTime
	 * @return Returns a Timestamp
	 */
	public Timestamp getStartTime()
	{
		return startTime;
	}
	/**
	 * Sets the startTime
	 * @param startTime The startTime to set
	 */
	public void setStartTime(Timestamp startTime)
	{
		this.startTime = startTime;
	}
	/**
	 * Gets the stopTime
	 * @return Returns a Timestamp
	 */
	public Timestamp getStopTime()
	{
		return stopTime;
	}
	/**
	 * Sets the stopTime
	 * @param stopTime The stopTime to set
	 */
	public void setStopTime(Timestamp stopTime)
	{
		this.stopTime = stopTime;
	}
	/**
	 * Gets the priority
	 * @return Returns a int
	 */
	public int getPriority()
	{
		return priority;
	}
	/**
	 * Sets the priority
	 * @param priority The priority to set
	 */
	public void setPriority(int priority)
	{
		this.priority = priority;
	}
	/**
	 * Gets the status
	 * @return Returns a String
	 */
	public String getStatus()
	{
		return status;
	}
	/**
	 * Sets the status
	 * @param status The status to set
	 */
	public void setStatus(String status)
	{
		this.status = status;
	}
	/**
	 * Gets the message
	 * @return Returns a String
	 */
	public String getMessage()
	{
		return message;
	}
	/**
	 * Sets the message
	 * @param message The message to set
	 */
	public void setMessage(String message)
	{
		this.message = message;
	}
	/**
	 * Gets the jobTypeName
	 * @return Returns a String
	 */
	public String getJobTypeName()
	{
		return jobTypeName;
	}
	/**
	 * Sets the jobTypeName
	 * @param jobTypeName The jobTypeName to set
	 */
	public void setJobTypeName(String jobTypeName)
	{
		this.jobTypeName = jobTypeName;
	}
}
