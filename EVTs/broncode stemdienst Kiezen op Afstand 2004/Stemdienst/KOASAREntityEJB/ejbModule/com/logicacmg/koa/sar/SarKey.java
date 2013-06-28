package com.logicacmg.koa.sar;
/**
 * Key class for Entity Bean: Sar
 */
public class SarKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: kiezeridentificatie
	 */
	public java.lang.String kiezeridentificatie;
	/**
	 * Creates an empty key for Entity Bean: Sar
	 */
	public SarKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Sar
	 */
	public SarKey(java.lang.String kiezeridentificatie)
	{
		this.kiezeridentificatie = kiezeridentificatie;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.sar.SarKey)
		{
			com.logicacmg.koa.sar.SarKey o =
				(com.logicacmg.koa.sar.SarKey) otherKey;
			return ((this.kiezeridentificatie.equals(o.kiezeridentificatie)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (kiezeridentificatie.hashCode());
	}
}
