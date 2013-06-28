package com.logicacmg.koa.scheduler.beans;
import java.rmi.RemoteException;

import com.logicacmg.koa.scheduler.beans.Jobtype;
/**
 * Home interface for Enterprise Bean: Scheduledjob
 */
public interface ScheduledjobHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: Scheduledjob
	 */
	public com.logicacmg.koa.scheduler.beans.Scheduledjob create(
		java.math.BigDecimal jobid)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	public com.logicacmg.koa.scheduler.beans.Scheduledjob create(
		java.math.BigDecimal jobid,
		Jobtype aJobtype,
		java.sql.Timestamp startTime,
		String status,
		String context,
		Integer priority)
		throws javax.ejb.CreateException, RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: Scheduledjob
	 */
	public com.logicacmg.koa.scheduler.beans.Scheduledjob findByPrimaryKey(
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration findScheduledjobByJobtype(
		com.logicacmg.koa.scheduler.beans.JobtypeKey inKey)
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}
