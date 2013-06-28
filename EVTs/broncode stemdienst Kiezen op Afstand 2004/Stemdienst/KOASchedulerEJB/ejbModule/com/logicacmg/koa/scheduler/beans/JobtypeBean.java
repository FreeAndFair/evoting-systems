package com.logicacmg.koa.scheduler.beans;
/**
 * Bean implementation class for Enterprise Bean: Jobtype
 */
public class JobtypeBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: typeid
	 */
	public java.math.BigDecimal typeid;
	/**
	 * Implemetation field for persistent attribute: name
	 */
	public java.lang.String name;
	/**
	 * Implemetation field for persistent attribute: firsttime
	 */
	public java.sql.Timestamp firsttime;
	/**
	 * Implemetation field for persistent attribute: interval
	 */
	public java.math.BigDecimal interval;
	/**
	 * Implemetation field for persistent attribute: successor
	 */
	public java.math.BigDecimal successor;
	/**
	 * Implemetation field for persistent attribute: implementationclass
	 */
	public java.lang.String implementationclass;
	/**
	 * Implemetation field for persistent attribute: defaultcontext
	 */
	public java.lang.String defaultcontext;
	/**
	 * Implemetation field for persistent attribute: priority
	 */
	public java.lang.Integer priority;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink scheduledjobLink;
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
	public com.logicacmg.koa.scheduler.beans.JobtypeKey ejbCreate(
		java.math.BigDecimal typeid)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.typeid = typeid;
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
	public void ejbPostCreate(java.math.BigDecimal typeid)
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
		scheduledjobLink = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		links.add(getScheduledjobLink());
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
	 * Get accessor for persistent attribute: name
	 */
	public java.lang.String getName()
	{
		return name;
	}
	/**
	 * Set accessor for persistent attribute: name
	 */
	public void setName(java.lang.String newName)
	{
		name = newName;
	}
	/**
	 * Get accessor for persistent attribute: firsttime
	 */
	public java.sql.Timestamp getFirsttime()
	{
		return firsttime;
	}
	/**
	 * Set accessor for persistent attribute: firsttime
	 */
	public void setFirsttime(java.sql.Timestamp newFirsttime)
	{
		firsttime = newFirsttime;
	}
	/**
	 * Get accessor for persistent attribute: interval
	 */
	public java.math.BigDecimal getInterval()
	{
		return interval;
	}
	/**
	 * Set accessor for persistent attribute: interval
	 */
	public void setInterval(java.math.BigDecimal newInterval)
	{
		interval = newInterval;
	}
	/**
	 * Get accessor for persistent attribute: successor
	 */
	public java.math.BigDecimal getSuccessor()
	{
		return successor;
	}
	/**
	 * Set accessor for persistent attribute: successor
	 */
	public void setSuccessor(java.math.BigDecimal newSuccessor)
	{
		successor = newSuccessor;
	}
	/**
	 * Get accessor for persistent attribute: implementationclass
	 */
	public java.lang.String getImplementationclass()
	{
		return implementationclass;
	}
	/**
	 * Set accessor for persistent attribute: implementationclass
	 */
	public void setImplementationclass(java.lang.String newImplementationclass)
	{
		implementationclass = newImplementationclass;
	}
	/**
	 * Get accessor for persistent attribute: defaultcontext
	 */
	public java.lang.String getDefaultcontext()
	{
		return defaultcontext;
	}
	/**
	 * Set accessor for persistent attribute: defaultcontext
	 */
	public void setDefaultcontext(java.lang.String newDefaultcontext)
	{
		defaultcontext = newDefaultcontext;
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
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException
	{
		this.getScheduledjobLink().secondaryAddElement(aScheduledjob);
	}
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException
	{
		this.getScheduledjobLink().secondaryRemoveElement(aScheduledjob);
	}
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink getScheduledjobLink()
	{
		if (scheduledjobLink == null)
			scheduledjobLink = new JobtypeToScheduledjobLink(this);
		return scheduledjobLink;
	}
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getScheduledjob()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return this.getScheduledjobLink().enumerationValue();
	}
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void addScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException
	{
		this.getScheduledjobLink().addElement(aScheduledjob);
	}
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void removeScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException
	{
		this.getScheduledjobLink().removeElement(aScheduledjob);
	}
}
