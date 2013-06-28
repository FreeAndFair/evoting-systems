package com.logicacmg.koa.scheduler.beans;
/**
 * Key class for Entity Bean: Scheduledjob
 */
public class ScheduledjobKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: jobid
	 */
	public java.math.BigDecimal jobid;
	/**
	 * Creates an empty key for Entity Bean: Scheduledjob
	 */
	public ScheduledjobKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Scheduledjob
	 */
	public ScheduledjobKey(java.math.BigDecimal jobid)
	{
		this.jobid = jobid;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey
			instanceof com.logicacmg.koa.scheduler.beans.ScheduledjobKey)
		{
			com.logicacmg.koa.scheduler.beans.ScheduledjobKey o =
				(com.logicacmg.koa.scheduler.beans.ScheduledjobKey) otherKey;
			return ((this.jobid.equals(o.jobid)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (jobid.hashCode());
	}
}
