package com.logicacmg.koa.esb.beans;
/**
 * Key class for Entity Bean: Esbfingerprints
 */
public class EsbfingerprintsKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: id
	 */
	public java.math.BigDecimal id;
	/**
	 * Creates an empty key for Entity Bean: Esbfingerprints
	 */
	public EsbfingerprintsKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Esbfingerprints
	 */
	public EsbfingerprintsKey(java.math.BigDecimal id)
	{
		this.id = id;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.esb.beans.EsbfingerprintsKey)
		{
			com.logicacmg.koa.esb.beans.EsbfingerprintsKey o =
				(com.logicacmg.koa.esb.beans.EsbfingerprintsKey) otherKey;
			return ((this.id.equals(o.id)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (id.hashCode());
	}
}
