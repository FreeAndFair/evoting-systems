package com.logicacmg.koa.kr.beans;
/**
 * Bean implementation class for Enterprise Bean: KRFingerprints
 */
public class KRFingerprintsBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: id
	 */
	public java.math.BigDecimal id;
	public java.lang.Short type;
	public byte[] fingerprint;
	/**
	 * Implemetation field for persistent attribute: timestamp
	 */
	public java.sql.Timestamp timestamp;
	/**
	 * Implemetation field for persistent attribute: systemstatus
	 */
	public java.lang.String systemstatus;
	/**
	 * getEntityContext
	 */
	public javax.ejb.EntityContext getEntityContext()
	{
		return myEntityCtx;
	}
	/**
	 * setEntityContext
	 */
	public void setEntityContext(javax.ejb.EntityContext ctx)
	{
		myEntityCtx = ctx;
	}
	/**
	 * unsetEntityContext
	 */
	public void unsetEntityContext()
	{
		myEntityCtx = null;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
		_initLinks();
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprintsKey ejbCreate()
		throws javax.ejb.CreateException
	{
		_initLinks();
		return null;
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprintsKey ejbCreate(
		java.math.BigDecimal xId,
		Short xType,
		byte[] xFingerprint,
		java.sql.Timestamp xTimestamp,
		java.lang.String sSystemState)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.id = xId;
		this.type = xType;
		this.fingerprint = xFingerprint;
		this.timestamp = xTimestamp;
		this.systemstatus = sSystemState;
		return null;
	}
	/**
	 * ejbLoad
	 */
	public void ejbLoad()
	{
		_initLinks();
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate() throws javax.ejb.CreateException
	{
	}
	public void ejbPostCreate(
		java.math.BigDecimal xId,
		Short xType,
		byte[] xFingerprint,
		java.sql.Timestamp xTimestamp,
		java.lang.String sSystemState)
		throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove() throws javax.ejb.RemoveException
	{
		try
		{
			_removeLinks();
		}
		catch (java.rmi.RemoteException e)
		{
			throw new javax.ejb.RemoveException(e.getMessage());
		}
	}
	/**
	 * ejbStore
	 */
	public void ejbStore()
	{
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected void _initLinks()
	{
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		return links;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected void _removeLinks()
		throws java.rmi.RemoteException, javax.ejb.RemoveException
	{
		java.util.List links = _getLinks();
		for (int i = 0; i < links.size(); i++)
		{
			try
			{
				((com.ibm.ivj.ejb.associations.interfaces.Link) links.get(i))
					.remove();
			}
			catch (javax.ejb.FinderException e)
			{
			} //Consume Finder error since I am going away
		}
	}
	/**
	 * Get accessor for persistent attribute: fingerprint
	 */
	public byte[] getFingerprint()
	{
		return fingerprint;
	}
	/**
	 * Set accessor for persistent attribute: fingerprint
	 */
	public void setFingerprint(byte[] newFingerprint)
	{
		fingerprint = newFingerprint;
	}
	/**
	 * Get accessor for persistent attribute: timestamp
	 */
	public java.sql.Timestamp getTimestamp()
	{
		return timestamp;
	}
	/**
	 * Set accessor for persistent attribute: timestamp
	 */
	public void setTimestamp(java.sql.Timestamp newTimestamp)
	{
		timestamp = newTimestamp;
	}
	/**
	 * Get accessor for persistent attribute: systemstatus
	 */
	public java.lang.String getSystemstatus()
	{
		return systemstatus;
	}
	/**
	 * Set accessor for persistent attribute: systemstatus
	 */
	public void setSystemstatus(java.lang.String newSystemstatus)
	{
		systemstatus = newSystemstatus;
	}
}
