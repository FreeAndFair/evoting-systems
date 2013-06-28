package com.logicacmg.koa.kr.beans;
/**
 * Home interface for Enterprise Bean: Transactioncode
 */
public interface TransactioncodeHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Transactioncode
	 */
	public com.logicacmg.koa.kr.beans.Transactioncode create(
		java.lang.String transactienummer)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Transactioncode
	 */
	public com.logicacmg.koa.kr.beans.Transactioncode findByPrimaryKey(
		com.logicacmg.koa.kr.beans.TransactioncodeKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
