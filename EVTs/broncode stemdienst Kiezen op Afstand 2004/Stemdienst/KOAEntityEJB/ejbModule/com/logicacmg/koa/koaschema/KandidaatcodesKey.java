package com.logicacmg.koa.koaschema;
/**
 * Key class for Entity Bean: Kandidaatcodes
 */
public class KandidaatcodesKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: kandidaatcode
	 */
	public java.lang.String kandidaatcode;
	/**
	 * Creates an empty key for Entity Bean: Kandidaatcodes
	 */
	public KandidaatcodesKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Kandidaatcodes
	 */
	public KandidaatcodesKey(java.lang.String kandidaatcode)
	{
		this.kandidaatcode = kandidaatcode;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.koaschema.KandidaatcodesKey)
		{
			com.logicacmg.koa.koaschema.KandidaatcodesKey o =
				(com.logicacmg.koa.koaschema.KandidaatcodesKey) otherKey;
			return ((this.kandidaatcode.equals(o.kandidaatcode)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (kandidaatcode.hashCode());
	}
}
