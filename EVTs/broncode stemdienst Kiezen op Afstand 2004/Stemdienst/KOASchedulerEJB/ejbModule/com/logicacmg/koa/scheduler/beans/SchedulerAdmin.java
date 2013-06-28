package com.logicacmg.koa.scheduler.beans;
import java.math.BigDecimal;
import java.util.Vector;

import com.logica.eplatform.error.EPlatformException;
/**
 * Remote interface for Enterprise Bean: SchedulerAdmin
 */
public interface SchedulerAdmin extends javax.ejb.EJBObject
{
	public void configureJobType(
		BigDecimal type,
		java.util.Date firstTime,
		BigDecimal interval)
		throws EPlatformException, java.rmi.RemoteException;
	public void rescheduleForJobType(BigDecimal successorType)
		throws EPlatformException, java.rmi.RemoteException;
	public void removeScheduledJob(BigDecimal jobID)
		throws EPlatformException, java.rmi.RemoteException;
	/**
	 * Reschedules for a certain jobtype
	 * 
	 * @param successorType The JobType id of the type to reschedule
	 * 
	 * @throws EPlatformException exception when something goes wrong during rescheduling
	 * 
	 */
	public void rescheduleForJobType(
		BigDecimal successorType,
		String sCustomContext)
		throws EPlatformException, java.rmi.RemoteException;
	public Vector pollForScheduledJobs()
		throws EPlatformException, java.rmi.RemoteException;
}
