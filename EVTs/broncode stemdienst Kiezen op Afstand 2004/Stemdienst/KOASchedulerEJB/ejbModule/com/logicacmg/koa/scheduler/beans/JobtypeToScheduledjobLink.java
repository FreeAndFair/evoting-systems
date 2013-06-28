package com.logicacmg.koa.scheduler.beans;
import java.util.Enumeration;

import javax.naming.NamingException;
/**
 * JobtypeToScheduledjobLink
 * @generated
 */
public class JobtypeToScheduledjobLink
	extends com.ibm.ivj.ejb.associations.links.SingleToManyLink
{
	/**
	 * @generated
	 */
	private static com
		.logicacmg
		.koa
		.scheduler
		.beans
		.ScheduledjobHome targetHome;
	/**
	 * @generated
	 */
	private static final java.lang.String targetHomeName = "Scheduledjob";
	/**
	 * Create a link instance with the passed source bean.
	 * @generated
	 */
	public JobtypeToScheduledjobLink(javax.ejb.EntityBean anEntityBean)
	{
		super(anEntityBean);
	}
	/**
	 * Get the target home for the link.
	 * @generated
	 */
	protected synchronized com
		.logicacmg
		.koa
		.scheduler
		.beans
		.ScheduledjobHome getTargetHome(
			com.ibm.ivj.ejb.associations.links.Link aLink)
		throws javax.naming.NamingException
	{
		if (targetHome == null)
			targetHome =
				(com
					.logicacmg
					.koa
					.scheduler
					.beans
					.ScheduledjobHome) lookupTargetHome("java:comp/env/ejb/Scheduledjob",
					com.logicacmg.koa.scheduler.beans.ScheduledjobHome.class);
		return targetHome;
	}
	/**
	 * Fetch the target for this many link, return an enumeration of the members.
	 * @generated
	 */
	protected java.util.Enumeration fetchTargetEnumeration()
		throws javax.ejb.FinderException, java.rmi.RemoteException
	{
		Enumeration enum = null;
		try
		{
			enum =
				(
					(com
						.logicacmg
						.koa
						.scheduler
						.beans
						.ScheduledjobHome) getTargetHome(
						this)).findScheduledjobByJobtype(
					(com
						.logicacmg
						.koa
						.scheduler
						.beans
						.JobtypeKey) getEntityContext()
						.getPrimaryKey());
		}
		catch (NamingException e)
		{
			throw new FinderException(e.toString());
		}
		return enum;
	}
	/**
	 * Get the entity context from the source bean.
	 * @generated
	 */
	public javax.ejb.EntityContext getEntityContext()
	{
		return ((com.logicacmg.koa.scheduler.beans.JobtypeBean) source)
			.getEntityContext();
	}
	/**
	 * Return whether or not the source key is valid for querying.
	 * @generated
	 */
	protected boolean isKeyValid()
	{
		return (getEntityContext().getPrimaryKey() != null);
	}
	/**
	 * Direct my counterLink to set my source as its target.
	 * @generated
	 */
	public void secondarySetCounterLinkOf(javax.ejb.EJBObject anEJB)
		throws java.rmi.RemoteException
	{
		if (anEJB != null)
			(
				(
					com
						.logicacmg
						.koa
						.scheduler
						.beans
						.Scheduledjob) anEJB)
						.secondarySetJobtype(
				(com.logicacmg.koa.scheduler.beans.Jobtype) getEntityContext()
					.getEJBObject());
	}
	/**
	 * Send my counterLink #secondaryDisconnect by routing through my target EJB.
	 * @generated
	 */
	public void setNullCounterLinkOf(javax.ejb.EJBObject anEJB)
		throws java.rmi.RemoteException
	{
		if (anEJB != null)
			(
				(
					com
						.logicacmg
						.koa
						.scheduler
						.beans
						.Scheduledjob) anEJB)
						.setJobtype(
				null);
	}
	/**
	 * Send my counterLink #secondaryDisconnect by routing through my target EJB.
	 * @generated
	 */
	public void secondarySetNullCounterLinkOf(javax.ejb.EJBObject anEJB)
		throws java.rmi.RemoteException
	{
		if (anEJB != null)
			(
				(
					com
						.logicacmg
						.koa
						.scheduler
						.beans
						.Scheduledjob) anEJB)
						.secondarySetJobtype(
				null);
	}
	/**
	 * Add an element to this many link.  Disallow null adds.
	 * @generated
	 */
	public void addElement(javax.ejb.EJBObject targetEJB)
		throws java.rmi.RemoteException
	{
		if (targetEJB != null)
		{
			super.addElement(targetEJB);
			(
				(
					com
						.logicacmg
						.koa
						.scheduler
						.beans
						.Scheduledjob) targetEJB)
						.privateSetJobtypeKey(
				(com
					.logicacmg
					.koa
					.scheduler
					.beans
					.JobtypeKey) getEntityContext()
					.getPrimaryKey());
		}
	}
	/**
	 * Narrow the remote object.
	 * @generated
	 */
	protected javax.ejb.EJBObject narrowElement(java.lang.Object element)
		throws java.rmi.RemoteException
	{
		return (EJBObject) javax.rmi.PortableRemoteObject.narrow(
			element,
			com.logicacmg.koa.scheduler.beans.Scheduledjob.class);
	}
	/**
	 * Check if I contain anEJB by comparing primary keys.
	 * @generated
	 */
	protected boolean currentlyContains(javax.ejb.EJBObject anEJB)
		throws java.rmi.RemoteException
	{
		return super.currentlyContains(anEJB)
			|| getEntityContext().getPrimaryKey().equals(
				((com.logicacmg.koa.scheduler.beans.Scheduledjob) anEJB)
					.getJobtypeKey());
	}
}
