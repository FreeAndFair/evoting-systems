package com.logicacmg.koa.koaschema;
/**
 * Home interface for Enterprise Bean: Kandidaatcodes
 */
public interface KandidaatcodesHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Kandidaatcodes
	 */
	public com.logicacmg.koa.koaschema.Kandidaatcodes create(
		java.lang.String kandidaatcode)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Creates an instance from a key for Entity Bean: Kandidaatcodes
	 */
	public com.logicacmg.koa.koaschema.Kandidaatcodes create(
		String kandidaatcode,
		String positienummer,
		String kieslijstnummer,
		String kieskringnummer)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Kandidaatcodes
	 */
	public com.logicacmg.koa.koaschema.Kandidaatcodes findByPrimaryKey(
		com.logicacmg.koa.koaschema.KandidaatcodesKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration findKandidaatcodesByFk_kkrklpn_1(
		com.logicacmg.koa.koaschema.LijstpositiesKey inKey)
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}
