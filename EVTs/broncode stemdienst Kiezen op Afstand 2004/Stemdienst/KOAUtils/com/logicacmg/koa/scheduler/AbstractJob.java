/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.AbstractJob.java
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
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.scheduler.Job;
import com.logicacmg.koa.scheduler.JobContext;
/**
 * Abstract job used as base for all jobs for the scheduler.
 */
public abstract class AbstractJob implements Job
{
	protected JobContext context;
	/**
	 * @see Job#setContext(JobContext)
	 */
	public void setContext(JobContext context)
	{
		this.context = context;
	}
	/**
	 * @see Job#getContext()
	 */
	public JobContext getContext()
	{
		return context;
	}
	/**
	 * @see Job#init()
	 */
	public abstract boolean init() throws EPlatformException;
}