package com.logicacmg.koa.koaschema;
/**
 * Home interface for Enterprise Bean: Kieskringen
 */
public interface KieskringenHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Kieskringen
	 */
	public com.logicacmg.koa.koaschema.Kieskringen create(
		java.lang.String kieskringnummer)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Kieskringen
	 */
	public com.logicacmg.koa.koaschema.Kieskringen findByPrimaryKey(
		com.logicacmg.koa.koaschema.KieskringenKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
