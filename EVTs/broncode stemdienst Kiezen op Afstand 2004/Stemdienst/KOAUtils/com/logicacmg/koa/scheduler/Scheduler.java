/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.Scheduler.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		25-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.util.Hashtable;
import java.util.Vector;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;
import javax.sql.DataSource;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.scheduler.beans.JobTarget;
import com.logicacmg.koa.scheduler.beans.JobTargetHome;
import com.logicacmg.koa.scheduler.beans.SchedulerAdmin;
import com.logicacmg.koa.scheduler.beans.SchedulerAdminHome;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The scheduler that is used to schedule certain tasks for
 * specified moments to be executed. This is the entrypoint
 * that will be started.
 * 
 * @author KuijerM
 */
public class Scheduler extends Thread
{
	public static final int SLEEP_INTERVAL = 15;
	private JobTargetHome ejbHome = null;
	private SchedulerAdminHome ejbAdminHome = null;
	private DataSource ds = null;
	private boolean requiredStatus = true;
	/**
	 * The public constructor for the scheduler
	 * In this method the EJB's are started, 
	 * connection is initialized and the scheduler is
	 * automatically started.
	 */
	public Scheduler()
	{
		initEJB();
		setRequiredStatus(true);
		this.start();
	}
	/**
	 * Initialize all the EJB's used by the scheduler
	 */
	private void initEJB()
	{
		try
		{
			Hashtable htProps = new Hashtable();
			htProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.SCHEDULER_CONTEXT_FACTORY));
			htProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.SCHEDULER_PROVIDER));
			InitialContext ic = new InitialContext(htProps);
			Object obj =
				ic.lookup(
					JNDIProperties.getProperty(
						JNDIProperties.SCHEDULER_JNDI_NAME));
			ejbHome =
				(JobTargetHome) PortableRemoteObject.narrow(
					obj,
					JobTargetHome.class);
			Object objAdmin =
				ic.lookup(
					JNDIProperties.getProperty(
						JNDIProperties.SCHEDULER_ADMIN_JNDI_NAME));
			ejbAdminHome =
				(SchedulerAdminHome) PortableRemoteObject.narrow(
					objAdmin,
					SchedulerAdminHome.class);
		}
		catch (NamingException ne)
		{
			String[] params = { "JobTarget and SchedulerAdmin" };
			KOALogHelper.logErrorCode(
				"Scheduler.initEJB",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"Scheduler.initEJB",
				"A "
					+ koae.getClass().getName()
					+ " was thrown. Message: "
					+ koae.getMessage(),
				koae);
		}
	}
	/**
	 * The run method for this Thread.
	 * This method executes all the jobs
	 */
	public void run()
	{
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"e-Platform Scheduler starting up");
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"------------------------------------");
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"Sleep interval = " + SLEEP_INTERVAL);
		while (requiredStatus)
		{
			try
			{
				// pause for interval secs.
				this.sleep(SLEEP_INTERVAL * 1000);
				// if to be stopped, break
				if (!requiredStatus)
					break;
				// do a cycle
				poll();
			}
			catch (Throwable t)
			{
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"A "
						+ t.getClass().getName()
						+ " was thrown "
						+ t.getMessage());
			}
		}
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"e-Platform Scheduler shutting down");
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"------------------------------------------------------");
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"Current jobs are finished properly. New jobs will be rejected");
	}
	/**
	 * Poll the database for new jobs to start
	 * if new jobs are found, the jobs are executed.
	 */
	private void poll()
	{
		try
		{
			SchedulerAdmin admin = ejbAdminHome.create();
			Vector vJobs = admin.pollForScheduledJobs();
			/* loop through all the jobs and execute the jobs */
			for (int i = 0; i < vJobs.size(); i++)
			{
				/* create new job target */
				JobTarget jobTarget = ejbHome.create();
				/* get job id */
				BigDecimal jobID = (BigDecimal) vJobs.elementAt(i);
				/* execute the job */
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[Scheduler] jobTarget.performExecute() for " + jobID);
				jobTarget.performExecute(jobID);
			}
		}
		catch (RemoteException re)
		{
			String[] params = { "JobTarget" };
			KOALogHelper.logErrorCode(
				"Scheduler.poll",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
		}
		catch (CreateException ce)
		{
			String[] params = { "JobTarget" };
			KOALogHelper.logErrorCode(
				"Scheduler.poll",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			initEJB();
		}
		catch (EPlatformException ep)
		{
			KOALogHelper.logError("Scheduler.poll", "poll", ep);
		}
	}
	/**
	 * set the required status.
	 * 
	 * @param newstatus The new status to set
	 */
	public void setRequiredStatus(boolean newstatus)
	{
		requiredStatus = newstatus;
	}
	/**
	 * get the required status
	 * 
	 * @return boolean the required status
	 */
	public boolean getRequiredStatus()
	{
		return requiredStatus;
	}
	/**
	 * Indicates if the scheduler is running
	 * 
	 */
	public boolean isRunning()
	{
		return this.isAlive();
	}
}