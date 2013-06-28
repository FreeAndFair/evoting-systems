package com.logicacmg.koa.scheduler.beans;
/**
 * Home interface for Enterprise Bean: Jobtype
 */
public interface JobtypeHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Jobtype
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype create(
		java.math.BigDecimal typeid)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Jobtype
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype findByPrimaryKey(
		com.logicacmg.koa.scheduler.beans.JobtypeKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
