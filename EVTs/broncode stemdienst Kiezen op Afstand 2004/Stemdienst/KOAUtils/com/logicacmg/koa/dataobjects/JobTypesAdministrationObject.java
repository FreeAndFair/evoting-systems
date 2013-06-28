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
import com.logicacmg.koa.dataobjects.JobTypeDataObject;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.scheduler.SchedulerConstants;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The administration object for the job types for the scheduler
 * 
 * @author KuijerM
 * 
 */
public class JobTypesAdministrationObject extends AbstractAdministrationObject
{
	/**
	 * Constructor for the job types administration object
	 * Initilializes the admin object.
	 * 
	 */
	public JobTypesAdministrationObject()
	{
		init();
	}
	/**
	 * Initialize the admin object.
	 * 
	 */
	private void init()
	{
		overviewJSP = "/JobTypesOverview.jsp";
	}
	/**
	 * Load the job types from the database
	 * 
	 * 
	 */
	protected void loadObjects()
	{
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
			String sqlQuery =
				"SELECT typeID, name, firstTime, interval, successor, priority from KOA01.JobType order by typeID";
			ResultSet rs = st.executeQuery(sqlQuery);
			while (rs.next()
				&& objects.size() < SchedulerConstants.MAX_RESULTS)
			{
				JobTypeDataObject job =
					new JobTypeDataObject(
						rs.getBigDecimal("typeID").setScale(0));
				job.setFirstTime(rs.getTimestamp("firstTime"));
				job.setInterval(rs.getBigDecimal("interval"));
				job.setName(rs.getString("name"));
				job.setPriority(rs.getInt("priority"));
				job.setSuccessor(rs.getBigDecimal("successor"));
				objects.add(job);
				objectsByKey.put(job.getJobTypeID().toString(), job);
			}
			isTruncated = rs.next();
		}
		catch (SQLException se)
		{
			String[] params = { "Problems loading objects from db" };
			KOALogHelper.logErrorCode(
				"JobTypesAdministrationObject.loadObjects",
				ErrorConstants.ERR_SQL,
				params,
				se);
		}
		catch (NamingException ne)
		{
			String[] params = { "datasource" };
			KOALogHelper.logErrorCode(
				"JobTypesAdministrationObject.loadObjects",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"JobTypesAdministrationObject.loadObjects",
				"Problems finding properties for loading objects",
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
					"[JobTypesAdministrationObject.loadObjects] Exception closing connection");
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
	 * disable the object
	 * This method is not implemented
	 * 
	 */
	public void disableObject(String key)
	{
	}
}