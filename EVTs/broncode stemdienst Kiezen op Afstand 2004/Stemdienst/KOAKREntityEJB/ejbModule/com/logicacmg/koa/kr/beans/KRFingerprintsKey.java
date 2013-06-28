package com.logicacmg.koa.kr.beans;
/**
 * Key class for Entity Bean: KRFingerprints
 */
public class KRFingerprintsKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: id
	 */
	public java.math.BigDecimal id;
	/**
	 * Creates an empty key for Entity Bean: KRFingerprints
	 */
	public KRFingerprintsKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Esbfingerprints
	 */
	public KRFingerprintsKey(java.math.BigDecimal id)
	{
		this.id = id;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.kr.beans.KRFingerprintsKey)
		{
			com.logicacmg.koa.kr.beans.KRFingerprintsKey o =
				(com.logicacmg.koa.kr.beans.KRFingerprintsKey) otherKey;
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
