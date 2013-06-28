package com.logicacmg.koa.kr.beans;
/**
 * Key class for Entity Bean: Kiezers
 */
public class KiezersKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: stemcode
	 */
	public java.lang.String stemcode;
	/**
	 * Creates an empty key for Entity Bean: Kiezers
	 */
	public KiezersKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Kiezers
	 */
	public KiezersKey(java.lang.String stemcode)
	{
		this.stemcode = stemcode;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.kr.beans.KiezersKey)
		{
			com.logicacmg.koa.kr.beans.KiezersKey o =
				(com.logicacmg.koa.kr.beans.KiezersKey) otherKey;
			return ((this.stemcode.equals(o.stemcode)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (stemcode.hashCode());
	}
}
