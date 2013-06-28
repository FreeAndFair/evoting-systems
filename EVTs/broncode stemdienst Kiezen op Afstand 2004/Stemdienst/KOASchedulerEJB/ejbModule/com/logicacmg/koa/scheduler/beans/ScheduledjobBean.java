package com.logicacmg.koa.scheduler.beans;
import com.logicacmg.koa.scheduler.beans.Jobtype;
import com.logicacmg.koa.scheduler.beans.ScheduledjobToJobtypeLink;
/**
 * Bean implementation class for Enterprise Bean: Scheduledjob
 */
public class ScheduledjobBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: jobid
	 */
	public java.math.BigDecimal jobid;
	/**
	 * Implemetation field for persistent attribute: starttime
	 */
	public java.sql.Timestamp starttime;
	/**
	 * Implemetation field for persistent attribute: stoptime
	 */
	public java.sql.Timestamp stoptime;
	/**
	 * Implemetation field for persistent attribute: priority
	 */
	public java.lang.Integer priority;
	/**
	 * Implemetation field for persistent attribute: status
	 */
	public java.lang.String status;
	/**
	 * Implemetation field for persistent attribute: retrycount
	 */
	public java.lang.Integer retrycount;
	/**
	 * Implemetation field for persistent attribute: lastupdate
	 */
	public java.sql.Timestamp lastupdate;
	/**
	 * Implemetation field for persistent attribute: context
	 */
	public java.lang.String context;
	/**
	 * Implemetation field for persistent attribute: message
	 */
	public java.lang.String message;
	/**
	 * Implemetation field for persistent attribute: jobtype_typeid
	 */
	public java.math.BigDecimal jobtype_typeid;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink jobtypeLink;
	/**
	 * getEntityContext
	 */
	public javax.ejb.EntityContext getEntityContext()
	{
		return myEntityCtx;
	}
	/**
	 * setEntityContext
	 */
	public void setEntityContext(javax.ejb.EntityContext ctx)
	{
		myEntityCtx = ctx;
	}
	/**
	 * unsetEntityContext
	 */
	public void unsetEntityContext()
	{
		myEntityCtx = null;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
		_initLinks();
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.scheduler.beans.ScheduledjobKey ejbCreate(
		java.math.BigDecimal jobid)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.jobid = jobid;
		return null;
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.scheduler.beans.ScheduledjobKey ejbCreate(
		java.math.BigDecimal jobid,
		Jobtype aJobtype,
		java.sql.Timestamp startTime,
		String status,
		String context,
		Integer priority)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.jobid = jobid;
		try
		{
			this.getJobtypeLink().set(aJobtype);
		}
		catch (java.rmi.RemoteException re)
		{
			throw new javax.ejb.CreateException(re.getMessage());
		}
		this.starttime = startTime;
		this.status = status;
		this.context = context;
		this.priority = priority;
		return null;
	}
	/**
	 * ejbLoad
	 */
	public void ejbLoad()
	{
		_initLinks();
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(java.math.BigDecimal jobid)
		throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(
		java.math.BigDecimal jobid,
		Jobtype aJobtype,
		java.sql.Timestamp startTime,
		String status,
		String context,
		Integer priority)
		throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove() throws javax.ejb.RemoveException
	{
		try
		{
			_removeLinks();
		}
		catch (java.rmi.RemoteException e)
		{
			throw new javax.ejb.RemoveException(e.getMessage());
		}
	}
	/**
	 * ejbStore
	 */
	public void ejbStore()
	{
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected void _initLinks()
	{
		jobtypeLink = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		links.add(getJobtypeLink());
		return links;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected void _removeLinks()
		throws java.rmi.RemoteException, javax.ejb.RemoveException
	{
		java.util.List links = _getLinks();
		for (int i = 0; i < links.size(); i++)
		{
			try
			{
				((com.ibm.ivj.ejb.associations.interfaces.Link) links.get(i))
					.remove();
			}
			catch (javax.ejb.FinderException e)
			{
			} //Consume Finder error since I am going away
		}
	}
	/**
	 * Get accessor for persistent attribute: starttime
	 */
	public java.sql.Timestamp getStarttime()
	{
		return starttime;
	}
	/**
	 * Set accessor for persistent attribute: starttime
	 */
	public void setStarttime(java.sql.Timestamp newStarttime)
	{
		starttime = newStarttime;
	}
	/**
	 * Get accessor for persistent attribute: stoptime
	 */
	public java.sql.Timestamp getStoptime()
	{
		return stoptime;
	}
	/**
	 * Set accessor for persistent attribute: stoptime
	 */
	public void setStoptime(java.sql.Timestamp newStoptime)
	{
		stoptime = newStoptime;
	}
	/**
	 * Get accessor for persistent attribute: priority
	 */
	public java.lang.Integer getPriority()
	{
		return priority;
	}
	/**
	 * Set accessor for persistent attribute: priority
	 */
	public void setPriority(java.lang.Integer newPriority)
	{
		priority = newPriority;
	}
	/**
	 * Get accessor for persistent attribute: status
	 */
	public java.lang.String getStatus()
	{
		return status;
	}
	/**
	 * Set accessor for persistent attribute: status
	 */
	public void setStatus(java.lang.String newStatus)
	{
		status = newStatus;
	}
	/**
	 * Get accessor for persistent attribute: retrycount
	 */
	public java.lang.Integer getRetrycount()
	{
		return retrycount;
	}
	/**
	 * Set accessor for persistent attribute: retrycount
	 */
	public void setRetrycount(java.lang.Integer newRetrycount)
	{
		retrycount = newRetrycount;
	}
	/**
	 * Get accessor for persistent attribute: lastupdate
	 */
	public java.sql.Timestamp getLastupdate()
	{
		return lastupdate;
	}
	/**
	 * Set accessor for persistent attribute: lastupdate
	 */
	public void setLastupdate(java.sql.Timestamp newLastupdate)
	{
		lastupdate = newLastupdate;
	}
	/**
	 * Get accessor for persistent attribute: context
	 */
	public java.lang.String getContext()
	{
		return context;
	}
	/**
	 * Set accessor for persistent attribute: context
	 */
	public void setContext(java.lang.String newContext)
	{
		context = newContext;
	}
	/**
	 * Get accessor for persistent attribute: message
	 */
	public java.lang.String getMessage()
	{
		return message;
	}
	/**
	 * Set accessor for persistent attribute: message
	 */
	public void setMessage(java.lang.String newMessage)
	{
		message = newMessage;
	}
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setJobtype(com.logicacmg.koa.scheduler.beans.Jobtype aJobtype)
		throws java.rmi.RemoteException
	{
		this.getJobtypeLink().set(aJobtype);
	}
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondarySetJobtype(
		com.logicacmg.koa.scheduler.beans.Jobtype aJobtype)
		throws java.rmi.RemoteException
	{
		this.getJobtypeLink().secondarySet(aJobtype);
	}
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink getJobtypeLink()
	{
		if (jobtypeLink == null)
			jobtypeLink = new ScheduledjobToJobtypeLink(this);
		return jobtypeLink;
	}
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.scheduler.beans.JobtypeKey getJobtypeKey()
	{
		com.logicacmg.koa.scheduler.beans.JobtypeKey temp =
			new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		boolean jobtype_NULLTEST = true;
		jobtype_NULLTEST &= (jobtype_typeid == null);
		temp.typeid = jobtype_typeid;
		if (jobtype_NULLTEST)
			temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetJobtypeKey(
		com.logicacmg.koa.scheduler.beans.JobtypeKey inKey)
	{
		boolean jobtype_NULLTEST = (inKey == null);
		jobtype_typeid = (jobtype_NULLTEST) ? null : inKey.typeid;
	}
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype getJobtype()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return (com.logicacmg.koa.scheduler.beans.Jobtype) this
			.getJobtypeLink()
			.value();
	}
}
