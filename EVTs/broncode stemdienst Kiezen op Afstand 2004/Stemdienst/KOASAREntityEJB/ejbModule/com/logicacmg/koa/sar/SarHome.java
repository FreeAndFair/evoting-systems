package com.logicacmg.koa.sar;
/**
 * Home interface for Enterprise Bean: Sar
 */
public interface SarHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Sar
	 */
	public com.logicacmg.koa.sar.Sar create(
		java.lang.String kiezeridentificatie,
		String stemcode)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Sar
	 */
	public com.logicacmg.koa.sar.Sar findByPrimaryKey(
		com.logicacmg.koa.sar.SarKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Sar
	 */
	public com.logicacmg.koa.sar.Sar findByStemcode(String sStemcode)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
