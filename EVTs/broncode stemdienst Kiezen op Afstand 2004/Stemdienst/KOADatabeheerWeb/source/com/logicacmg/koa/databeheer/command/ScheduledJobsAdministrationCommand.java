/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.voorzitter.command.ScheduledJobsAdministrationCommand.java
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
package com.logicacmg.koa.databeheer.command;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.databeheer.command.AbstractAdministrationCommand;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.dataobjects.ScheduledJobsAdministrationObject;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Command for administration of the Scheduled Jobs for the scheduler
 * 
 * @author KuijerM
 * 
 */
public class ScheduledJobsAdministrationCommand
	extends AbstractAdministrationCommand
{
	// which report
	private String jobID = null, status = null;
	/**
	 * Initialize the command and read all parameters from request
	 * if an overview object is set in the session, the object is read from session
	 * parameters that can be provided: 
	 * 	'id' Selected key
	 *  'page' The page number
	 * 	'status' The status to search for
	 * 	'jobID' The job id to search for
	 * 
	 * @param request javax.servlet.http.HttpServletRequest
	 * 
	 */
	public void init(javax.servlet.http.HttpServletRequest request)
		throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ScheduledJobsAdministrationCommand] init");
		super.init(request);
		// retrieve search criteria
		//
		Object o = null;
		o = request.getParameter("status");
		if (o != null)
			status = o.toString();
		o = request.getParameter("jobID");
		if (o != null)
			jobID = o.toString();
		// retrieve the overview if available
		//
		Object obj =
			request.getSession().getAttribute(
				CommandConstants.ADMIN_OBJECT_IN_SESSION);
		if (obj != null && obj instanceof ScheduledJobsAdministrationObject)
			overview = (ScheduledJobsAdministrationObject) obj;
	}
	/**
	 * Executes the command in the container
	 * 
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ScheduledJobsAdministrationCommand] execute");
		// if we find params, create a new one with params
		if (jobID != null && (status != null))
		{
			// check input...
			//
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[RequestOverviewCommand] New search object generated");
			overview = new ScheduledJobsAdministrationObject(jobID, status);
			overview.search();
		}
		// else, show the appropriate key of the current one if available
		else if (overview != null && pageNo != 1)
		{
			// do nothing
			KOALogHelper.log(KOALogHelper.TRACE, "Overview object reused");
		}
		// refresh
		else if (overview != null && pageNo == 1)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"Refresh Overview, with current Settings");
			overview.search();
		}
		// New one needed
		else
		{
			overview = new ScheduledJobsAdministrationObject();
			overview.search();
		}
	}
}