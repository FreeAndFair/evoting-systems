package com.logicacmg.koa.koaschema;
/**
 * Bean implementation class for Enterprise Bean: Districten
 */
public class DistrictenBean implements javax.ejb.EntityBean {
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: districtnummer
	 */
	public java.lang.String districtnummer;
	/**
	 * Implemetation field for persistent attribute: districtnaam
	 */
	public java.lang.String districtnaam;
	/**
	 * Implemetation field for persistent attribute: fk_dist_kkr_kieskringnummer
	 */
	public java.lang.String fk_dist_kkr_kieskringnummer;
	private transient com.ibm.ivj.ejb.associations.interfaces.SingleLink fk_dist_kkrLink;
	/**
	 * getEntityContext
	 */
	public javax.ejb.EntityContext getEntityContext() {
		return myEntityCtx;
	}
	/**
	 * setEntityContext
	 */
	public void setEntityContext(javax.ejb.EntityContext ctx) {
		myEntityCtx = ctx;
	}
	/**
	 * unsetEntityContext
	 */
	public void unsetEntityContext() {
		myEntityCtx = null;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate() {
		_initLinks();
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.koaschema.DistrictenKey ejbCreate(java.lang.String districtnummer) throws javax.ejb.CreateException {
		_initLinks();
		this.districtnummer = districtnummer;
		return null;
	}
	/**
	 * ejbLoad
	 */
	public void ejbLoad() {
		_initLinks();
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate() {
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(java.lang.String districtnummer) throws javax.ejb.CreateException {
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove() throws javax.ejb.RemoveException {
		try {
			_removeLinks();
		} catch (java.rmi.RemoteException e) {
			throw new javax.ejb.RemoveException(e.getMessage());
		}
	}
	/**
	 * ejbStore
	 */
	public void ejbStore() {
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected void _initLinks() {
		fk_dist_kkrLink = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks() {
		java.util.Vector links = new java.util.Vector();
		links.add(getFk_dist_kkrLink());
		return links;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected void _removeLinks() throws java.rmi.RemoteException, javax.ejb.RemoveException {
		java.util.List links = _getLinks();
		for (int i = 0; i < links.size() ; i++) {
			try {
				((com.ibm.ivj.ejb.associations.interfaces.Link) links.get(i)).remove();
			} catch (javax.ejb.FinderException e) {} //Consume Finder error since I am going away
		}
	}
	/**
	 * Get accessor for persistent attribute: districtnaam
	 */
	public java.lang.String getDistrictnaam() {
		return districtnaam;
	}
	/**
	 * Set accessor for persistent attribute: districtnaam
	 */
	public void setDistrictnaam(java.lang.String newDistrictnaam) {
		districtnaam = newDistrictnaam;
	}
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setFk_dist_kkr(com.logicacmg.koa.koaschema.Kieskringen aFk_dist_kkr) throws java.rmi.RemoteException {
		this.getFk_dist_kkrLink().set(aFk_dist_kkr);
	}
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondarySetFk_dist_kkr(com.logicacmg.koa.koaschema.Kieskringen aFk_dist_kkr) throws java.rmi.RemoteException {
		this.getFk_dist_kkrLink().secondarySet(aFk_dist_kkr);
	}
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com.ibm.ivj.ejb.associations.interfaces.SingleLink getFk_dist_kkrLink() {
		if (fk_dist_kkrLink == null)
		fk_dist_kkrLink = new DistrictenToFk_dist_kkrLink(this);
		return fk_dist_kkrLink;
	}
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey getFk_dist_kkrKey() {
		com.logicacmg.koa.koaschema.KieskringenKey temp = new com.logicacmg.koa.koaschema.KieskringenKey();
		boolean fk_dist_kkr_NULLTEST = true;
		fk_dist_kkr_NULLTEST &= (fk_dist_kkr_kieskringnummer == null);
		temp.kieskringnummer = fk_dist_kkr_kieskringnummer;
		if (fk_dist_kkr_NULLTEST) temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_dist_kkrKey(com.logicacmg.koa.koaschema.KieskringenKey inKey) {
		boolean fk_dist_kkr_NULLTEST = (inKey == null);
		fk_dist_kkr_kieskringnummer = (fk_dist_kkr_NULLTEST) ? null : inKey.kieskringnummer;
	}
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Kieskringen getFk_dist_kkr() throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.koaschema.Kieskringen)this.getFk_dist_kkrLink().value();
	}
}
