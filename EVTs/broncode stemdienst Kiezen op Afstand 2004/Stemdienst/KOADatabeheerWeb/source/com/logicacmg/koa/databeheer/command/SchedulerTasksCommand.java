/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.voorzitter.command.SchedulerTasksCommand.java
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
package com.logicacmg.koa.databeheer.command;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Hashtable;
import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;
import com.logica.eplatform.command.AbstractTargetableCommand;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.scheduler.SchedulerConstants;
import com.logicacmg.koa.scheduler.beans.SchedulerAdmin;
import com.logicacmg.koa.scheduler.beans.SchedulerAdminHome;
import com.logicacmg.koa.utils.KOALogHelper;
public class SchedulerTasksCommand
	extends AbstractTargetableCommand
	implements HttpCommand
{
	// which report
	private String action = null,
		date = null,
		hours = null,
		minutes = null,
		interval = null;
	private String jobID = null;
	/**
	 * Initialize the command and read all parameters from request
	 * if an overview object is set in the session, the object is read from session
	 * parameters that can be provided: 
	 * 	'id' Selected key
	 *  'page' The page number
	 * 	'action' The action to execute, possible values: DELETE, NEW, collect_counters
	 * 	'date' The date for the job in format dd-MM-yyyy
	 * 	'hours' The hours value for the scheduled job values 0-23
	 * 	'minutes' The minutes value for the scheduled job values 0-59
	 * 	'interval' The interval in hours
	 * 	'jobID' the job id to use
	 * 
	 * @param request javax.servlet.http.HttpServletRequest
	 * 
	 */
	public void init(javax.servlet.http.HttpServletRequest request)
		throws EPlatformException
	{
		KOALogHelper.log(KOALogHelper.INFO, "[SchedulerTasksCommand] init");
		// retrieve parameters
		//
		action = request.getParameter("action");
		date = request.getParameter("date");
		hours = request.getParameter("hours");
		minutes = request.getParameter("minutes");
		interval = request.getParameter("interval");
		jobID = request.getParameter("jobID");
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[SchedulerTasksCommand] got parameters: action = ["
				+ action
				+ "] date = ["
				+ date
				+ "] hours = ["
				+ hours
				+ "] minutes = ["
				+ minutes
				+ "] interval = ["
				+ interval
				+ "] jobid = ["
				+ jobID
				+ "]");
	}
	/**
	 * Executes the command in the container
	 * 
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		KOALogHelper.log(KOALogHelper.INFO, "[SchedulerTasksCommand] execute");
		if (action != null)
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
					JNDIProperties.getProperty(
						JNDIProperties.SCHEDULER_PROVIDER));
				InitialContext ic = new InitialContext(htProps);
				Object remoteObj =
					ic.lookup(
						JNDIProperties.getProperty(
							JNDIProperties.SCHEDULER_ADMIN_JNDI_NAME));
				SchedulerAdminHome schedulerHome =
					(SchedulerAdminHome) PortableRemoteObject.narrow(
						remoteObj,
						SchedulerAdminHome.class);
				SchedulerAdmin admin = schedulerHome.create();
				if (action.equals(SchedulerConstants.ACTION_DELETE))
				{
					if (jobID != null)
					{
						admin.removeScheduledJob(new BigDecimal(jobID));
					}
				}
				else
				{
					Date dtDate = null;
					if ((date == null) || (date.equals("")))
					{
						//get the date of today at 0:00 based on the system time
						dtDate =
							new SimpleDateFormat(
								SchedulerConstants.DATE_FORMAT).parse(
								new SimpleDateFormat(
									SchedulerConstants.DATE_FORMAT).format(
									new Date(System.currentTimeMillis())));
					}
					else
					{
						dtDate =
							new SimpleDateFormat(
								SchedulerConstants.DATE_FORMAT).parse(
								date);
					}
					dtDate =
						new Date(
							dtDate.getTime()
								+ Long.parseLong(hours) * 60 * 60 * 1000
								+ Long.parseLong(minutes) * 60 * 1000);
					BigDecimal intervalBD =
						new BigDecimal(interval).multiply(new BigDecimal(60));
					BigDecimal jobType = null;
					//TODO: if actions are added here, please add the actions also in the docs in the init after 'action'
					if (action
						.equals(SchedulerConstants.ACTION_COLLECT_COUNTERS))
					{
						jobType =
							new BigDecimal(
								SchedulerConstants
									.JOB_TYPE_ID_COLLECT_COUNTERS);
					}
					else
					{
						return;
					}
					admin.configureJobType(jobType, dtDate, intervalBD);
					admin.rescheduleForJobType(jobType);
				}
			}
			catch (NamingException ne)
			{
				String[] params = { "SchedulerAdmin" };
				KOALogHelper.logErrorCode(
					"SchedulerTasksCommand.execute",
					ErrorConstants.ERR_NAMING,
					params,
					ne);
				throw new EPlatformException("schedulertaskcmd_exec", ne);
			}
			catch (RemoteException re)
			{
				String[] params = { "SchedulerAdmin" };
				KOALogHelper.logErrorCode(
					"SchedulerTasksCommand.execute",
					ErrorConstants.ERR_REMOTE,
					params,
					re);
				throw new EPlatformException("schedulertaskcmd_exec", re);
			}
			catch (CreateException ce)
			{
				String[] params = { "SchedulerAdmin" };
				KOALogHelper.logErrorCode(
					"SchedulerTasksCommand.execute",
					ErrorConstants.ERR_CREATE,
					params,
					ce);
				throw new EPlatformException("schedulertaskcmd_exec", ce);
			}
			catch (ParseException e)
			{
				KOALogHelper.logError(
					"SchedulerTasksCommand.execute",
					"ParseException message: " + e.getMessage(),
					e);
				throw new EPlatformException("schedulertaskcmd_exec", e);
			}
		}
	}
	/**
	 * returns the result page url
	 * redirects to the scheduledJobsOverview if action is delete
	 * Else redirect to the schedulerTasks
	 * 
	 * 
	 */
	public String getResultJSP()
	{
		if (action != null && action.equals(SchedulerConstants.ACTION_DELETE))
		{
			return "ScheduledJobsOverview";
		}
		else
		{
			return "SchedulerTasks.jsp";
		}
	}
	/**
	 * Insert the method's description here.
	 * Creation date: (20-2-2001 14:24:17)
	 * @return java.lang.String
	 */
	public String getErrorJSP()
	{
		return CommandConstants.DEFAULT_ERROR_JSP;
	}
	public void updateSession(HttpSession session)
	{
	}
}
