package com.logicacmg.koa.controller.beans;
/**
 * Key class for Entity Bean: Koa_state
 */
public class Koa_stateKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: id
	 */
	public java.lang.Integer id;
	/**
	 * Creates an empty key for Entity Bean: Koa_state
	 */
	public Koa_stateKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Koa_state
	 */
	public Koa_stateKey(java.lang.Integer id)
	{
		this.id = id;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey
			instanceof com.logicacmg.koa.controller.beans.Koa_stateKey)
		{
			com.logicacmg.koa.controller.beans.Koa_stateKey o =
				(com.logicacmg.koa.controller.beans.Koa_stateKey) otherKey;
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
