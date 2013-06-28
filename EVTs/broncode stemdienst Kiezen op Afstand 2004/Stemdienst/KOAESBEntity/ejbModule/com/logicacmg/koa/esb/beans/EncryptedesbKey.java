package com.logicacmg.koa.esb.beans;
/**
 * Key class for Entity Bean: Encryptedesb
 */
public class EncryptedesbKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: stemnummer
	 */
	public java.math.BigDecimal stemnummer;
	/**
	 * Creates an empty key for Entity Bean: Encryptedesb
	 */
	public EncryptedesbKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Encryptedesb
	 */
	public EncryptedesbKey(java.math.BigDecimal stemnummer)
	{
		this.stemnummer = stemnummer;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.esb.beans.EncryptedesbKey)
		{
			com.logicacmg.koa.esb.beans.EncryptedesbKey o =
				(com.logicacmg.koa.esb.beans.EncryptedesbKey) otherKey;
			return ((this.stemnummer.equals(o.stemnummer)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (stemnummer.hashCode());
	}
}
