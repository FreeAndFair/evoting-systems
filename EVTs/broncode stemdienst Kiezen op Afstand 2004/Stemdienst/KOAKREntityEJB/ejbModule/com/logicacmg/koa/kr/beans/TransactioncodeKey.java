package com.logicacmg.koa.kr.beans;
/**
 * Key class for Entity Bean: Transactioncode
 */
public class TransactioncodeKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implementation field for persistent attribute: transactienummer
	 */
	public java.lang.String transactienummer;
	/**
	 * Creates a key for Entity Bean: Transactioncode
	 */
	public TransactioncodeKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Transactioncode
	 */
	public TransactioncodeKey(java.lang.String transactienummer)
	{
		this.transactienummer = transactienummer;
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.kr.beans.TransactioncodeKey)
		{
			com.logicacmg.koa.kr.beans.TransactioncodeKey o =
				(com.logicacmg.koa.kr.beans.TransactioncodeKey) otherKey;
			return ((this.transactienummer.equals(o.transactienummer)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (transactienummer.hashCode());
	}
}
