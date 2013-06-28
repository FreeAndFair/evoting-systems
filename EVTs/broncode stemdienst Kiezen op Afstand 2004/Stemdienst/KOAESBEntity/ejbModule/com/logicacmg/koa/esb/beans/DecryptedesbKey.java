package com.logicacmg.koa.esb.beans;
/**
 * Key class for Entity Bean: Decryptedesb
 */
public class DecryptedesbKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: stemnummer
	 */
	public java.math.BigDecimal stemnummer;
	/**
	 * Creates an empty key for Entity Bean: Decryptedesb
	 */
	public DecryptedesbKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Decryptedesb
	 */
	public DecryptedesbKey(java.math.BigDecimal stemnummer)
	{
		this.stemnummer = stemnummer;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.esb.beans.DecryptedesbKey)
		{
			com.logicacmg.koa.esb.beans.DecryptedesbKey o =
				(com.logicacmg.koa.esb.beans.DecryptedesbKey) otherKey;
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
