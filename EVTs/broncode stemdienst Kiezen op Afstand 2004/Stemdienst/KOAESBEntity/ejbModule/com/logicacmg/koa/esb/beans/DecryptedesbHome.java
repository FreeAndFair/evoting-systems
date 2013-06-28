package com.logicacmg.koa.esb.beans;
/**
 * Home interface for Enterprise Bean: Decryptedesb
 */
public interface DecryptedesbHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Decryptedesb
	 */
	public com.logicacmg.koa.esb.beans.Decryptedesb create(
		java.math.BigDecimal stemnummer)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	public com.logicacmg.koa.esb.beans.Decryptedesb create(
		java.math.BigDecimal stemnummer,
		java.lang.String sKandidaatCode,
		java.lang.String sKieskringnummer,
		java.lang.String sDistrictnummer,
		java.lang.String sKieslijstnummer,
		java.lang.String sPositienummer,
		java.lang.String sLijstnaam,
		java.lang.String sAchternaam,
		java.lang.String sVoorletters)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Decryptedesb
	 */
	public com.logicacmg.koa.esb.beans.Decryptedesb findByPrimaryKey(
		com.logicacmg.koa.esb.beans.DecryptedesbKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Decryptedesb
	 */
	public com.logicacmg.koa.esb.beans.Decryptedesb findByLijstpositie(
		java.lang.String sKieskringnummer,
		java.lang.String sKieslijstnummer,
		java.lang.String sPositienummer)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
