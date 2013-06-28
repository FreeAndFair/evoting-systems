/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.beans.JobTargetBean.java
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
  *  0.1		15-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler.beans;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.sql.Connection;
import java.sql.Timestamp;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.scheduler.Job;
import com.logicacmg.koa.scheduler.JobContext;
import com.logicacmg.koa.scheduler.SchedulerConstants;
import com.logicacmg.koa.scheduler.beans.Jobtype;
import com.logicacmg.koa.scheduler.beans.JobtypeHome;
import com.logicacmg.koa.scheduler.beans.JobtypeKey;
import com.logicacmg.koa.scheduler.beans.Scheduledjob;
import com.logicacmg.koa.scheduler.beans.ScheduledjobHome;
import com.logicacmg.koa.scheduler.beans.ScheduledjobKey;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Bean implementation class for Enterprise Bean: JobTarget
 * 
 */
public class JobTargetBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	private ScheduledjobHome scheduledjobHome = null;
	private ControllerHome controllerHome = null;
	private JobtypeHome jobtypeHome = null;
	private UserTransaction userTX = null;
	private Connection con = null;
	/**
	 * getSessionContext
	 */
	public javax.ejb.SessionContext getSessionContext()
	{
		return mySessionCtx;
	}
	/**
	 * setSessionContext
	 */
	public void setSessionContext(javax.ejb.SessionContext ctx)
	{
		mySessionCtx = ctx;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
	}
	/**
	 * ejbCreate
	 */
	public void ejbCreate() throws javax.ejb.CreateException
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[JobTargetBean] create....");
		// get the UserTransaction		
		userTX = getSessionContext().getUserTransaction();
		// get references to the ScheduledJob and JobType beans
		try
		{
			Hashtable htSchedulerProps = new Hashtable();
			htSchedulerProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.SCHEDULER_CONTEXT_FACTORY));
			htSchedulerProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.SCHEDULER_PROVIDER));
			Hashtable htControllerProps = new Hashtable();
			htControllerProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
			htControllerProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
			InitialContext icScheduler = new InitialContext(htSchedulerProps);
			InitialContext icController = new InitialContext(htControllerProps);
			// lookup Scheduledjob
			Object jobObj =
				icScheduler.lookup(
					JNDIProperties.getProperty(
						JNDIProperties.SCHEDULED_JOB_JNDI_NAME));
			scheduledjobHome =
				(ScheduledjobHome) PortableRemoteObject.narrow(
					jobObj,
					ScheduledjobHome.class);
			// lookup Joptype
			Object jobtypeObj =
				icScheduler.lookup(
					JNDIProperties.getProperty(
						JNDIProperties.JOB_TYPE_JNDI_NAME));
			jobtypeHome =
				(JobtypeHome) PortableRemoteObject.narrow(
					jobtypeObj,
					JobtypeHome.class);
			// lookup PrimaryKeyGenerator
			Object controllerObj =
				icController.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			controllerHome =
				(ControllerHome) javax.rmi.PortableRemoteObject.narrow(
					controllerObj,
					ControllerHome.class);
		}
		catch (NamingException ne)
		{
			String[] params = { "scheduledjob and Jobtype and controller" };
			KOALogHelper.logErrorCode(
				"JobTargetBean.create",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new CreateException(ne.getMessage());
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"JobTargetBean.create",
				"KOAEException during create",
				koae);
			throw new CreateException(koae.getMessage());
		}
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove()
	{
	}
	/**
	 * Performs the execution of the scheduled job.
	 * 
	 * @param jobID The id of the job to execute.
	 * 
	 * @throws EPlatformException Exception when something goes wrong during execution
	 * 
	 */
	public void performExecute(BigDecimal jobID) throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[JobTargetBean] performExecute ....");
		Scheduledjob sJob = null;
		Job job = null;
		JobContext context = null;
		boolean bErrorInit = false;
		try
		{
			userTX.setTransactionTimeout(
				Integer.parseInt(
					TechnicalProps.getProperty(
						TechnicalProps.SCHEDULE_TX_TIMEOUT)));
			// start first transaction	
			userTX.begin();
			// get job details and create the Job
			sJob =
				scheduledjobHome.findByPrimaryKey(new ScheduledjobKey(jobID));
			job =
				(Job) Class
					.forName(sJob.getJobtype().getImplementationclass())
					.newInstance();
			// set the context 
			context = new JobContext(sJob.getContext());
			job.setContext(context);
			// init the job.
			if (!job.init())
			{
				try
				{
					if (sJob.getRetrycount().intValue() < 3)
					{
						sJob.setStarttime(
							new Timestamp(
								sJob.getStarttime().getTime()
									+ (60 * 60 * 1000)));
						sJob.setRetrycount(
							new Integer((sJob.getRetrycount().intValue() + 1)));
					}
					else
					{
						sJob.setStatus(SchedulerConstants.STATUS_ABORTED);
						sJob.setMessage(SchedulerConstants.INIT_ERROR_MESSAGE);
					}
					userTX.commit();
					return;
				}
				catch (Exception e)
				{
					KOALogHelper.logError("JobTargetBean", "performExecute", e);
					throw new EPlatformException("jobtarget_execute", e);
				}
			}
			// update job status
			sJob.setStatus(SchedulerConstants.STATUS_PROCESSING);
			// commit first transaction
			userTX.commit();
		}
		catch (FinderException fe)
		{
			bErrorInit = true;
			String[] params = { "ScheduledJob" };
			KOALogHelper.logErrorCode(
				"JobTargetBean",
				ErrorConstants.ERR_FINDER,
				params,
				fe);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_JOBTARGET_EXECUTE,
				fe);
		}
		catch (RemoteException re)
		{
			bErrorInit = true;
			String[] params = { "ScheduledJob" };
			KOALogHelper.logErrorCode(
				"JobTargetBean",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_JOBTARGET_EXECUTE,
				re);
		}
		catch (Exception e)
		{
			bErrorInit = true;
			KOALogHelper.logErrorCode(
				"JobTargetBean",
				ErrorConstants.ERR_SCHEDULER_EXECUTE_SCHEDULED_JOB,
				e);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_JOBTARGET_EXECUTE,
				e);
		}
		// added for more consistent handling of status
		finally
		{
			if (bErrorInit)
			{
				try
				{
					userTX.setTransactionTimeout(
						Integer.parseInt(
							TechnicalProps.getProperty(
								TechnicalProps.SCHEDULE_TX_TIMEOUT)));
					/* start a new transaction for the setting of the job stats */
					userTX.begin();
					// update job context, update time
					sJob.setContext(job.getContext().getXMLString());
					sJob.setLastupdate(getCurrentDBTime());
					// create successor and set status
					createSuccessorJob(sJob);
					sJob.setStatus(SchedulerConstants.STATUS_ABORTED);
					// commit transaction before returning
					userTX.commit();
				}
				catch (Exception e)
				{
					KOALogHelper.logError(
						"JobTargetBean",
						"performExecute in init",
						e);
					throw new EPlatformException("jobtarget_execute", e);
				}
			}
		}
		try
		{
			boolean finished = false;
			userTX.setTransactionTimeout(
				Integer.parseInt(
					TechnicalProps.getProperty(
						TechnicalProps.SCHEDULE_TX_TIMEOUT)));
			// start TX
			userTX.begin();
			// execute job
			try
			{
				finished = job.execute();
			}
			catch (Exception e)
			{
				KOALogHelper.logError(
					"JobTargetBean.performExecute",
					"Job not finished properly, aborting job",
					e);
				finished = false;
			}
			try
			{
				int status = userTX.getStatus();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[JobTargetBean] checking TX status for execution of the job: "
						+ status);
				if ((status == Status.STATUS_MARKED_ROLLBACK))
				{
					//rollback the transaction
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[JobTargetBean] Rollback the transaction because of wrong transaciton status");
					userTX.rollback();
					// update the job status
					sJob.setStatus(SchedulerConstants.STATUS_ABORTED);
				}
				else
				{
					if (finished)
					{
						// commit if finished properly
						userTX.commit();
					}
					else
					{
						//rollback if the transaction has not finised properly
						userTX.rollback();
					}
				}
			}
			catch (Exception e)
			{
				KOALogHelper.logErrorCode(
					"JobTargetBean",
					ErrorConstants.ERR_SCHEDULER_EXECUTE_SCHEDULED_JOB,
					e);
				throw new EPlatformException(
					ErrorConstants.SCHEDULER_JOBTARGET_EXECUTE,
					e);
			}
			/* start a new transaction for the setting of the job stats */
			userTX.begin();
			// update job context, update time
			sJob.setContext(job.getContext().getXMLString());
			sJob.setLastupdate(getCurrentDBTime());
			// create successor and set status
			if (finished)
			{
				createSuccessorJob(sJob);
				sJob.setMessage(job.getContext().getMessage());
				sJob.setStoptime(getCurrentDBTime());
				sJob.setStatus(SchedulerConstants.STATUS_PROCESSED);
			}
			else
			{
				createSuccessorJob(sJob);
				sJob.setStoptime(getCurrentDBTime());
				sJob.setStatus(SchedulerConstants.STATUS_ABORTED);
			}
		}
		catch (EPlatformException ep)
		{
			throw ep;
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"JobTargetBean",
				ErrorConstants.ERR_SCHEDULER_EXECUTE_SCHEDULED_JOB,
				e);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_JOBTARGET_EXECUTE,
				e);
		}
		finally
		{
			try
			{
				int status = userTX.getStatus();
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[JobTargetBean] checking TX status: " + status);
				if ((userTX.getStatus() == Status.STATUS_MARKED_ROLLBACK))
				{
					// update the job status
					sJob.setStatus(SchedulerConstants.STATUS_ABORTED);
				}
				// commit the user tx
				userTX.commit();
			}
			catch (Exception e)
			{
				KOALogHelper.logError("JobTargetBean", "performExecute", e);
				throw new EPlatformException(
					ErrorConstants.SCHEDULER_JOBTARGET_EXECUTE,
					e);
			}
		}
	}
	/**
	 * create Successor creates a new Job after the job has been successfully executed.
	 * The successorJob uses the defaultcontext for his jobType.
	 */
	private void createSuccessorJob(Scheduledjob sJob)
		throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[JobTargetBean] create successor");
		try
		{
			// check if the job has a successor
			BigDecimal successorType = sJob.getJobtype().getSuccessor();
			if (successorType == null)
			{
				return;
			}
			// get the successor details
			Jobtype jobType =
				jobtypeHome.findByPrimaryKey(new JobtypeKey(successorType));
			BigDecimal interval = jobType.getInterval();
			Timestamp startTime = sJob.getStarttime();
			Timestamp firstTime = jobType.getFirsttime();
			Timestamp newStartTime = null;
			if (firstTime != null)
			{
				long div = new java.util.Date().getTime() - firstTime.getTime();
				long intervalLong = interval.longValue() * 60 * 1000;
				long intervTimes = (div / intervalLong) + 1;
				newStartTime =
					new Timestamp(
						firstTime.getTime() + (intervTimes * intervalLong));
			}
			else
			{
				newStartTime = new Timestamp(new java.util.Date().getTime());
			}
			// create the new successor
			Controller controller = controllerHome.create();
			BigDecimal key =
				BigDecimal.valueOf((long) controller.getNextSequenceNumber());
			Scheduledjob newJob =
				scheduledjobHome.create(
					key,
					jobType,
					newStartTime,
					SchedulerConstants.STATUS_SCHEDULED,
					jobType.getDefaultcontext(),
					jobType.getPriority());
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[JobTargetBean] successor created with key: "
					+ key
					+ " jobType "
					+ ((JobtypeKey) jobType.getPrimaryKey()).typeid);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"JobTargetBean.createSuccessorJob",
				ErrorConstants.ERR_SCHEDULER_CREATE_SUCCESSOR_JOB,
				e);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_CREATE_SUCCESSOR,
				e);
		}
	}
	private Timestamp getCurrentDBTime()
	{
		return new Timestamp(System.currentTimeMillis());
	}
}