package com.logicacmg.koa.scheduler.beans;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Timestamp;
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
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.scheduler.SchedulerConstants;
import com.logicacmg.koa.scheduler.beans.Jobtype;
import com.logicacmg.koa.scheduler.beans.JobtypeHome;
import com.logicacmg.koa.scheduler.beans.JobtypeKey;
import com.logicacmg.koa.scheduler.beans.Scheduledjob;
import com.logicacmg.koa.scheduler.beans.ScheduledjobHome;
import com.logicacmg.koa.scheduler.beans.ScheduledjobKey;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Bean implementation class for Enterprise Bean: SchedulerAdmin
 */
public class SchedulerAdminBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	private ScheduledjobHome scheduledjobHome = null;
	private JobtypeHome jobtypeHome = null;
	private ControllerHome controllerHome = null;
	private DataSource ds = null;
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
		try
		{
			Hashtable htSchedulerProps = new Hashtable();
			Hashtable htControllerProps = new Hashtable();
			Hashtable htDSProps = new Hashtable();
			htSchedulerProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.SCHEDULER_CONTEXT_FACTORY));
			htSchedulerProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.SCHEDULER_PROVIDER));
			htControllerProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
			htControllerProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
			htDSProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.DATASOURCE_CONTEXT_FACTORY));
			htDSProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_PROVIDER));
			InitialContext icScheduler = new InitialContext(htSchedulerProps);
			InitialContext icController = new InitialContext(htControllerProps);
			InitialContext icDataSource = new InitialContext(htDSProps);
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
			// lookup the datasource
			ds =
				(DataSource) icDataSource.lookup(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		}
		catch (NamingException ne)
		{
			String[] params = { "Datasources, JobType, Controller" };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean.create",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new CreateException(ne.getMessage());
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"SchedulerAdminBean.create",
				"error creating schedulerAdmin bean",
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
	 * Configures a jobtype
	 * 
	 * @param type The id of the type to configure
	 * @param firstTime The first time it should be scheduled
	 * @param interval The interval in minutes.
	 * 
	 * @throws EPlatformException Exception when something goes wrong during configuration.
	 * 
	 */
	public void configureJobType(
		BigDecimal type,
		java.util.Date firstTime,
		BigDecimal interval)
		throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SchedulerAdminBean.configureJobType] starting configureJobType");
		try
		{
			Jobtype jobType =
				jobtypeHome.findByPrimaryKey(new JobtypeKey(type));
			jobType.setFirsttime(new java.sql.Timestamp(firstTime.getTime()));
			jobType.setInterval(interval);
		}
		catch (FinderException fe)
		{
			String[] params = { "Jobtype with key " + type };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean",
				ErrorConstants.ERR_FINDER,
				params,
				fe);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_CONFIG_JOB,
				fe);
		}
		catch (RemoteException re)
		{
			String[] params = { "Jobtype" };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_CONFIG_JOB,
				re);
		}
		return;
	}
	public void rescheduleForJobType(BigDecimal successorType)
		throws EPlatformException
	{
		this.rescheduleForJobType(successorType, null);
	}
	/**
	 * Reschedules for a certain jobtype
	 * 
	 * @param successorType The JobType id of the type to reschedule
	 * @param sCustomContext The context to use for the scheduled job
	 * 
	 * @throws EPlatformException exception when something goes wrong during rescheduling
	 * 
	 */
	public void rescheduleForJobType(
		BigDecimal successorType,
		String sCustomContext)
		throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[SchedulerAdminBean.rescheduleForJobType] rescheduleForJobType");
		Connection con = null;
		String sContext = sCustomContext;
		try
		{
			con = ds.getConnection();
			Statement st = con.createStatement();
			int results =
				st.executeUpdate(
					"delete from KOA01.ScheduledJob where jobType = "
						+ successorType
						+ " and status = '"
						+ SchedulerConstants.STATUS_SCHEDULED
						+ "'");
			// get the successor details
			Jobtype jobType =
				jobtypeHome.findByPrimaryKey(new JobtypeKey(successorType));
			Timestamp currentTime = new Timestamp(System.currentTimeMillis());
			Timestamp firstTime = jobType.getFirsttime();
			/* check the context */
			if (sContext == null)
			{
				sContext = jobType.getDefaultcontext();
			}
			Timestamp newStartTime = null;
			if (firstTime != null)
			{
				newStartTime = firstTime;
			}
			else
			{
				// schedule ASAP
				//
				newStartTime = currentTime;
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[SchedulerAdminBean.rescheduleForJobType] No first time found, schedule asap");
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
					sContext,
					jobType.getPriority());
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SchedulerAdminBean.rescheduleForJobType] successor created with key: "
					+ key
					+ " jobType "
					+ ((JobtypeKey) jobType.getPrimaryKey()).typeid);
		}
		catch (SQLException se)
		{
			String[] params =
				{ "Reschedule for job with type " + successorType };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				se);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_RESCHEDULE_JOB,
				se);
		}
		catch (FinderException fe)
		{
			String[] params = { "Jobtype with key " + successorType };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean",
				ErrorConstants.ERR_FINDER,
				params,
				fe);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_RESCHEDULE_JOB,
				fe);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_RESCHEDULE_JOB,
				ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller or jobtype" };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_RESCHEDULE_JOB,
				re);
		}
		finally
		{
			try
			{
				con.close();
			}
			catch (Exception e)
			{ // You can't say I didn't try...
			}
		}
		return;
	}
	/**
	 * Removes a scheduled job from the list of scheduled jobs
	 * 
	 * @param jobID the job id of the job to remove
	 * 
	 * @throws EPlatformException Exception when something goes wrong during removal.
	 * 
	 */
	public void removeScheduledJob(BigDecimal jobID) throws EPlatformException
	{
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[SchedulerAdminBean] removeScheduledJob");
			Scheduledjob job =
				scheduledjobHome.findByPrimaryKey(new ScheduledjobKey(jobID));
			job.remove();
		}
		catch (FinderException fe)
		{
			String[] params = { "ScheduledJob with key " + jobID };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean.removeScheduledJob",
				ErrorConstants.ERR_FINDER,
				params,
				fe);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_REMOVE_JOB,
				fe);
		}
		catch (RemoteException re)
		{
			String[] params = { "ScheduledJob" };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean.removeScheduledJob",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_REMOVE_JOB,
				re);
		}
		catch (RemoveException rem)
		{
			String[] params = { "ScheduledJob with ID " + jobID };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean.removeScheduledJob",
				ErrorConstants.ERR_REMOVE_ENTITY,
				params,
				rem);
			throw new EPlatformException(
				ErrorConstants.SCHEDULER_REMOVE_JOB,
				rem);
		}
	}
	public Vector pollForScheduledJobs() throws EPlatformException
	{
		Vector vJobs = new Vector();
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		// poll the database
		Connection con = null;
		PreparedStatement st = null;
		ResultSet rs = null;
		try
		{
			//con = ds.getConnection();
			con = xDBUtils.getConnection();
			con.setReadOnly(true);
			st =
				con.prepareStatement(
					"Select jobID from KOA01.ScheduledJob where status = 'SCHEDULED' and startTime <= ? ");
			st.setTimestamp(1, new Timestamp(System.currentTimeMillis()));
			rs = st.executeQuery();
			/* loop through results	and add job ids to the list */
			while (rs.next())
			{
				// get an instance of the JobTarget (every job get it's own instance!!)
				BigDecimal jobID = rs.getBigDecimal("jobID");
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[SchedulerAdminBean.poll] adding job to list " + jobID);
				vJobs.add(jobID);
			}
			/* close everything */
			xDBUtils.closeResultSet(rs);
			xDBUtils.closeStatement(st);
			xDBUtils.closeConnection(con);
			con = null;
		}
		catch (SQLException se)
		{
			String[] params = { "polling for scheduled jobs in the db" };
			KOALogHelper.logErrorCode(
				"SchedulerAdminBean.poll",
				ErrorConstants.ERR_SQL,
				params,
				se);
			throw new EPlatformException("default", se);
		}
		catch (EPlatformException ep)
		{
			KOALogHelper.logError("SchedulerAdminBean.poll", "poll", ep);
			throw ep;
		}
		finally
		{
			/* close everything */
			xDBUtils.closeResultSet(rs);
			xDBUtils.closeStatement(st);
			xDBUtils.closeConnection(con);
			con = null;
		}
		return vJobs;
	}
}