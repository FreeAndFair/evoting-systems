package com.logicacmg.koa.koaschema;
/**
 * Remote interface for Enterprise Bean: Kieslijsten
 */
public interface Kieslijsten extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: lijstnaam
	 */
	public java.lang.String getLijstnaam() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: lijstnaam
	 */
	public void setLijstnaam(java.lang.String newLijstnaam)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey getFk_kkr_1Key()
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Kieskringen getFk_kkr_1()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddLijstposities(
		com.logicacmg.koa.koaschema.Lijstposities aLijstposities)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveLijstposities(
		com.logicacmg.koa.koaschema.Lijstposities aLijstposities)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getLijstposities()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}
