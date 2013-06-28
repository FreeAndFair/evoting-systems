package com.logicacmg.koa.scheduler.beans;
/**
 * Key class for Entity Bean: Jobtype
 */
public class JobtypeKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: typeid
	 */
	public java.math.BigDecimal typeid;
	/**
	 * Creates an empty key for Entity Bean: Jobtype
	 */
	public JobtypeKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Jobtype
	 */
	public JobtypeKey(java.math.BigDecimal typeid)
	{
		this.typeid = typeid;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.scheduler.beans.JobtypeKey)
		{
			com.logicacmg.koa.scheduler.beans.JobtypeKey o =
				(com.logicacmg.koa.scheduler.beans.JobtypeKey) otherKey;
			return ((this.typeid.equals(o.typeid)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (typeid.hashCode());
	}
}
