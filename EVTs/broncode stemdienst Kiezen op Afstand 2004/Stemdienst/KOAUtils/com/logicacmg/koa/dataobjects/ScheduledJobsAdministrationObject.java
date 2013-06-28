/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.JobTypesAdministrationObject.java
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
  *  0.1		28-04-2003	MKu	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.sql.DataSource;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.dataobjects.AbstractAdministrationObject;
import com.logicacmg.koa.dataobjects.ScheduledJobDataObject;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.scheduler.SchedulerConstants;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The administration object for the scheduled jobs used by the scheduler
 * 
 * @author KuijerM
 * 
 */
public class ScheduledJobsAdministrationObject
	extends AbstractAdministrationObject
{
	String jobID = "", status = "All";
	/**
	 * Constructor for the scheduled jobs administration object
	 * Initilializes the admin object.
	 * 
	 */
	public ScheduledJobsAdministrationObject()
	{
		init();
	}
	/**
	 * Constructor for the scheduled jobs administration object
	 * Initilializes the admin object.
	 * 
	 * @param jobID the job id to use for loading objects
	 * @param status the status to use to load objects
	 * 
	 */
	public ScheduledJobsAdministrationObject(String jobID, String status)
	{
		this.jobID = jobID;
		this.status = status;
		init();
	}
	/**
	 * Initialize the admin object.
	 * 
	 */
	private void init()
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ScheduledJobsAdministrationObject] init");
		overviewJSP = "/SchedulerJobs.jsp";
	}
	/**
	 * Load the scheduled jobs from the database
	 * if specified using the job ID and status in 
	 * the search
	 * 
	 */
	protected void loadObjects()
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ScheduledJobsAdministrationObject] loadObjects");
		StringBuffer whereClause = new StringBuffer();
		if (!jobID.equals(""))
			whereClause.append("jobID=" + jobID + " AND ");
		if (!status.equals("All"))
			whereClause.append("status='" + status + "' AND ");
		whereClause.append("1=1");
		Connection c = null;
		try
		{
			Hashtable htProps = new Hashtable();
			htProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.DATASOURCE_CONTEXT_FACTORY));
			htProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_PROVIDER));
			InitialContext ic = new InitialContext(htProps);
			DataSource ds =
				(DataSource) ic.lookup(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			c = ds.getConnection();
			Statement st = c.createStatement();
			st.setMaxRows(SchedulerConstants.MAX_RESULTS + 1);
			/*
			String sqlQuery = "SELECT SJ.jobID, SJ.jobType, SJ.startTime, SJ.stopTime, SJ.status, JT.name from KOA01.ScheduledJob SJ, KOA01.JobType JT where SJ.jobType = JT.typeID AND "+whereClause.toString() + " order by jobID desc";
			*/
			String sqlQuery =
				"SELECT SJ.jobID, SJ.jobType, SJ.startTime, SJ.stopTime, SJ.status, JT.name from KOA01.ScheduledJob SJ, KOA01.JobType JT where SJ.jobType = JT.typeID AND "
					+ whereClause.toString()
					+ " order by SJ.startTime desc";
			ResultSet rs = st.executeQuery(sqlQuery);
			while (rs.next()
				&& objects.size() < SchedulerConstants.MAX_RESULTS)
			{
				ScheduledJobDataObject job =
					new ScheduledJobDataObject(
						rs.getBigDecimal("jobID").setScale(0));
				job.setJobType(rs.getBigDecimal("jobType"));
				job.setStartTime(rs.getTimestamp("startTime"));
				job.setStopTime(rs.getTimestamp("stopTime"));
				job.setStatus(rs.getString("status"));
				job.setJobTypeName(rs.getString("name"));
				objects.add(job);
				objectsByKey.put(job.getJobID().toString(), job);
			}
			isTruncated = rs.next();
		}
		catch (SQLException se)
		{
			KOALogHelper.logErrorCode(
				"ScheduledJobsAdministrationObject.loadObjects",
				ErrorConstants.ERR_LOAD_OBJECTS,
				se);
		}
		catch (NamingException ne)
		{
			KOALogHelper.logErrorCode(
				"ScheduledJobsAdministrationObject.loadObjects",
				ErrorConstants.ERR_LOAD_OBJECTS,
				ne);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logErrorCode(
				"ScheduledJobsAdministrationObject.loadObjects",
				ErrorConstants.ERR_LOAD_OBJECTS_PROPS,
				koae);
		}
		finally
		{
			try
			{
				c.close();
			}
			catch (Exception e)
			{
				// you can't say I didn't try... 
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[ScheduledJobsAdministrationObject] An exception was thrown closing a connection");
			}
		}
	}
	/**
	 * update the object
	 * This method is not implemented
	 * 
	 */
	public void updateObject(String key)
	{
	}
	/**
	 * disables the object
	 * This method is not implemented
	 * 
	 */
	public void disableObject(String key)
	{
	}
	/**
	 * Get the job id that is deliverd in the constructor
	 * Empty String is returned if no Job ID specified.
	 * 
	 * @return String the job id
	 * 
	 */
	public String getJobID()
	{
		return jobID;
	}
	/**
	 * Get the status that is deliverd in the constructor
	 * If no status is specified 'All' is returned.
	 * 
	 * @return String the status used for the search
	 * 
	 */
	public String getStatus()
	{
		return status;
	}
}
