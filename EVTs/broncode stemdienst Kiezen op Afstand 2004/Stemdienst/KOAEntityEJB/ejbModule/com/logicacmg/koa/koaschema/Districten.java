package com.logicacmg.koa.koaschema;
/**
 * Remote interface for Enterprise Bean: Districten
 */
public interface Districten extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: districtnaam
	 */
	public java.lang.String getDistrictnaam() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: districtnaam
	 */
	public void setDistrictnaam(java.lang.String newDistrictnaam)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondarySetFk_dist_kkr(
		com.logicacmg.koa.koaschema.Kieskringen aFk_dist_kkr)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setFk_dist_kkr(
		com.logicacmg.koa.koaschema.Kieskringen aFk_dist_kkr)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey getFk_dist_kkrKey()
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_dist_kkrKey(
		com.logicacmg.koa.koaschema.KieskringenKey inKey)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_dist_kkr.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Kieskringen getFk_dist_kkr()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}