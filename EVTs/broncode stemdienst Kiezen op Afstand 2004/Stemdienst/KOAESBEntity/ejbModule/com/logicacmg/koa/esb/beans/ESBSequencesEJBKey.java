package com.logicacmg.koa.esb.beans;
/**
 * Key class for Entity Bean: ESBSequencesEJB
 */
public class ESBSequencesEJBKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: tablename
	 */
	public java.lang.String tablename;
	/**
	 * Creates an empty key for Entity Bean: ESBSequencesEJB
	 */
	public ESBSequencesEJBKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: ESBSequencesEJB
	 */
	public ESBSequencesEJBKey(java.lang.String tablename)
	{
		this.tablename = tablename;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.esb.beans.ESBSequencesEJBKey)
		{
			com.logicacmg.koa.esb.beans.ESBSequencesEJBKey o =
				(com.logicacmg.koa.esb.beans.ESBSequencesEJBKey) otherKey;
			return ((this.tablename.equals(o.tablename)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (tablename.hashCode());
	}
}
