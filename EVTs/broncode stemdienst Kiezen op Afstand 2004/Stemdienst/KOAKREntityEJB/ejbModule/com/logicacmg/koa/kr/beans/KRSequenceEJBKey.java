package com.logicacmg.koa.kr.beans;
/**
 * Key class for Entity Bean: KRSequenceEJB
 */
public class KRSequenceEJBKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: tablename
	 */
	public java.lang.String tablename;
	/**
	 * Creates an empty key for Entity Bean: KRSequenceEJB
	 */
	public KRSequenceEJBKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: KRSequenceEJB
	 */
	public KRSequenceEJBKey(String tablename)
	{
		this.tablename = tablename;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.kr.beans.KRSequenceEJBKey)
		{
			com.logicacmg.koa.kr.beans.KRSequenceEJBKey o =
				(com.logicacmg.koa.kr.beans.KRSequenceEJBKey) otherKey;
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
