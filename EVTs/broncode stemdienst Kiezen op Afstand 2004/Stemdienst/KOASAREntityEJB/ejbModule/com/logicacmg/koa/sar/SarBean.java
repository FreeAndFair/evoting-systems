package com.logicacmg.koa.sar;
/**
 * Bean implementation class for Enterprise Bean: Sar
 */
public class SarBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: kiezeridentificatie
	 */
	public java.lang.String kiezeridentificatie;
	/**
	 * Implemetation field for persistent attribute: stemcode
	 */
	public java.lang.String stemcode;
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
	//	/**
	//	 * ejbCreate method for a CMP entity bean.
	//	 */
	//	public com.logicacmg.koa.sar.SarKey ejbCreate(java.lang.String kiezeridentificatie) throws javax.ejb.CreateException {
	//		_initLinks();
	//		this.kiezeridentificatie = kiezeridentificatie;
	//		return null;
	//	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.sar.SarKey ejbCreate(
		java.lang.String kiezeridentificatie,
		String stemcode)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.stemcode = stemcode;
		this.kiezeridentificatie = kiezeridentificatie;
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
	//	/**
	//	 * ejbPostCreate
	//	 */
	//	public void ejbPostCreate(java.lang.String kiezeridentificatie) throws javax.ejb.CreateException {
	//	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(
		java.lang.String kiezeridentificatie,
		String stemcode)
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
	 * Get accessor for persistent attribute: stemcode
	 */
	public java.lang.String getStemcode()
	{
		return stemcode;
	}
	/**
	 * Set accessor for persistent attribute: stemcode
	 */
	public void setStemcode(java.lang.String newStemcode)
	{
		stemcode = newStemcode;
	}
}
