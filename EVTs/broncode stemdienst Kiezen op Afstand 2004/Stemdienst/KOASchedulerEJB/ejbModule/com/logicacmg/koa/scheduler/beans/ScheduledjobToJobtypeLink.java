package com.logicacmg.koa.scheduler.beans;
import javax.naming.NamingException;
/**
 * ScheduledjobToJobtypeLink
 * @generated
 */
public class ScheduledjobToJobtypeLink
	extends com.ibm.ivj.ejb.associations.links.ManyToSingleLink
{
	/**
	 * @generated
	 */
	private static com.logicacmg.koa.scheduler.beans.JobtypeHome targetHome;
	/**
	 * @generated
	 */
	private static final java.lang.String targetHomeName = "Jobtype";
	/**
	 * Create a link instance with the passed source bean.
	 * @generated
	 */
	public ScheduledjobToJobtypeLink(javax.ejb.EntityBean anEntityBean)
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
		.JobtypeHome getTargetHome(
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
					.JobtypeHome) lookupTargetHome("java:comp/env/ejb/Jobtype",
					com.logicacmg.koa.scheduler.beans.JobtypeHome.class);
		return targetHome;
	}
	/**
	 * Fetch the target for this single link, return an instance of the target class.
	 * @generated
	 */
	protected javax.ejb.EJBObject fetchTarget()
		throws javax.ejb.FinderException, java.rmi.RemoteException
	{
		EJBObject target = null;
		com.logicacmg.koa.scheduler.beans.JobtypeKey key =
			((com.logicacmg.koa.scheduler.beans.ScheduledjobBean) source)
				.getJobtypeKey();
		try
		{
			target =
				(
					(com
						.logicacmg
						.koa
						.scheduler
						.beans
						.JobtypeHome) getTargetHome(
						this)).findByPrimaryKey(
					key);
		}
		catch (NamingException e)
		{
			throw new FinderException(e.toString());
		}
		return target;
	}
	/**
	 * Get the entity context from the source bean.
	 * @generated
	 */
	public javax.ejb.EntityContext getEntityContext()
	{
		return ((com.logicacmg.koa.scheduler.beans.ScheduledjobBean) source)
			.getEntityContext();
	}
	/**
	 * Return whether or not the source key is valid for querying.
	 * @generated
	 */
	protected boolean isKeyValid()
	{
		return (
			((com.logicacmg.koa.scheduler.beans.ScheduledjobBean) source)
				.getJobtypeKey()
				!= null);
	}
	/**
	 * Forward inverse maintenance through my target EJB.
	 * @generated
	 */
	public void secondaryRemoveElementCounterLinkOf(javax.ejb.EJBObject anEJB)
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
						.Jobtype) anEJB)
						.secondaryRemoveScheduledjob(
				(com
					.logicacmg
					.koa
					.scheduler
					.beans
					.Scheduledjob) getEntityContext()
					.getEJBObject());
	}
	/**
	 * Forward inverse maintenance through my target EJB.
	 * @generated
	 */
	public void secondaryAddElementCounterLinkOf(javax.ejb.EJBObject anEJB)
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
						.Jobtype) anEJB)
						.secondaryAddScheduledjob(
				(com
					.logicacmg
					.koa
					.scheduler
					.beans
					.Scheduledjob) getEntityContext()
					.getEJBObject());
	}
	/**
	 * Set the target for this single link, an instance of the target class.
	 * @generated
	 */
	public void set(javax.ejb.EJBObject targetEJB)
		throws java.rmi.RemoteException
	{
		super.set(targetEJB);
		if (targetEJB == null)
			(
				(
					com
						.logicacmg
						.koa
						.scheduler
						.beans
						.ScheduledjobBean) source)
						.privateSetJobtypeKey(
				null);
		else
			(
				(
					com
						.logicacmg
						.koa
						.scheduler
						.beans
						.ScheduledjobBean) source)
						.privateSetJobtypeKey(
				(com.logicacmg.koa.scheduler.beans.JobtypeKey) targetEJB
					.getPrimaryKey());
	}
	/**
	 * Reset my target key.
	 * @generated
	 */
	protected void resetKey() throws java.rmi.RemoteException
	{
		(
			(
				com
					.logicacmg
					.koa
					.scheduler
					.beans
					.ScheduledjobBean) source)
					.privateSetJobtypeKey(
			null);
	}
}
