package com.logicacmg.koa.koaschema;
/**
 * Remote interface for Enterprise Bean: Kieskringen
 */
public interface Kieskringen extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: kieskringnaam
	 */
	public java.lang.String getKieskringnaam() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: kieskringnaam
	 */
	public void setKieskringnaam(java.lang.String newKieskringnaam)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getDistricten()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void addDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void removeDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddKieslijsten(
		com.logicacmg.koa.koaschema.Kieslijsten aKieslijsten)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveKieslijsten(
		com.logicacmg.koa.koaschema.Kieslijsten aKieslijsten)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getKieslijsten()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}
