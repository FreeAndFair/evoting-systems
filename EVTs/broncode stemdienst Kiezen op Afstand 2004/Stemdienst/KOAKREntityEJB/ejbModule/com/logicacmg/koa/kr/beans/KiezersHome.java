package com.logicacmg.koa.kr.beans;
/**
 * Home interface for Enterprise Bean: Kiezers
 */
public interface KiezersHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Kiezers
	 */
	public com.logicacmg.koa.kr.beans.Kiezers create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Creates an instance from a key for Entity Bean: Kiezers
	 */
	public com.logicacmg.koa.kr.beans.Kiezers create(
		String sStemcode,
		String sKiezersidentificatie,
		String sHashedWachtwoord,
		String sDistrictnummer,
		String sKieskringnummer,
		String sTransactienummer)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Kiezers
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByPrimaryKey(
		com.logicacmg.koa.kr.beans.KiezersKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Kiezers
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByKiezerId(String sKiezerId)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
