package com.logicacmg.koa.koaschema;
/**
 * Home interface for Enterprise Bean: Lijstposities
 */
public interface LijstpositiesHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Lijstposities
	 */
	public com.logicacmg.koa.koaschema.Lijstposities create(
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1,
		String achternaam,
		String voorletters,
		String roepnaam,
		char geslacht,
		String woonplaats)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Creates an instance from a key for Entity Bean: Lijstposities
	 */
	public com.logicacmg.koa.koaschema.Lijstposities create(
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Lijstposities
	 */
	public com.logicacmg.koa.koaschema.Lijstposities findByPrimaryKey(
		com.logicacmg.koa.koaschema.LijstpositiesKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration findLijstpositiesByFk_klkr_1(
		com.logicacmg.koa.koaschema.KieslijstenKey inKey)
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}
