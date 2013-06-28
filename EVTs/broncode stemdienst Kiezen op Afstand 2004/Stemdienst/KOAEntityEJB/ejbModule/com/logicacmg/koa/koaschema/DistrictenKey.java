package com.logicacmg.koa.koaschema;
/**
 * Key class for Entity Bean: Districten
 */
public class DistrictenKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: districtnummer
	 */
	public java.lang.String districtnummer;
	/**
	 * Creates an empty key for Entity Bean: Districten
	 */
	public DistrictenKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Districten
	 */
	public DistrictenKey(java.lang.String districtnummer)
	{
		this.districtnummer = districtnummer;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.koaschema.DistrictenKey)
		{
			com.logicacmg.koa.koaschema.DistrictenKey o =
				(com.logicacmg.koa.koaschema.DistrictenKey) otherKey;
			return ((this.districtnummer.equals(o.districtnummer)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (districtnummer.hashCode());
	}
}
