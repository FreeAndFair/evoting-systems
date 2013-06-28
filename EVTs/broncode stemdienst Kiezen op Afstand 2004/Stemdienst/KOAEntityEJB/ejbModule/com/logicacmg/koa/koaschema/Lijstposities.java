package com.logicacmg.koa.koaschema;
/**
 * Remote interface for Enterprise Bean: Lijstposities
 */
public interface Lijstposities extends javax.ejb.EJBObject
{
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getKandidaatcodes()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void addKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void removeKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieslijstenKey getFk_klkr_1Key()
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Kieslijsten getFk_klkr_1()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
	/**
	 * Get accessor for persistent attribute: achternaam
	 */
	public java.lang.String getAchternaam() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: achternaam
	 */
	public void setAchternaam(java.lang.String newAchternaam)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: voorletters
	 */
	public java.lang.String getVoorletters() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: voorletters
	 */
	public void setVoorletters(java.lang.String newVoorletters)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: roepnaam
	 */
	public java.lang.String getRoepnaam() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: roepnaam
	 */
	public void setRoepnaam(java.lang.String newRoepnaam)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: geslacht
	 */
	public char getGeslacht() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: geslacht
	 */
	public void setGeslacht(char newGeslacht) throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: woonplaats
	 */
	public java.lang.String getWoonplaats() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: woonplaats
	 */
	public void setWoonplaats(java.lang.String newWoonplaats)
		throws java.rmi.RemoteException;
}
