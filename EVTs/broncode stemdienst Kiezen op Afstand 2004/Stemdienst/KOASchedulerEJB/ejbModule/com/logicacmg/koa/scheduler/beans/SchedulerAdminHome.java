package com.logicacmg.koa.scheduler.beans;
/**
 * Home interface for Enterprise Bean: SchedulerAdmin
 */
public interface SchedulerAdminHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: SchedulerAdmin
	 */
	public com.logicacmg.koa.scheduler.beans.SchedulerAdmin create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
