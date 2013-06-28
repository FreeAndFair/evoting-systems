package com.logicacmg.koa.koaschema;
import java.util.Enumeration;

import javax.naming.NamingException;
/**
 * KieskringenToDistrictenLink
 * @generated
 */
public class KieskringenToDistrictenLink
	extends com.ibm.ivj.ejb.associations.links.SingleToManyLink
{
	/**
	 * @generated
	 */
	private static com.logicacmg.koa.koaschema.DistrictenHome targetHome;
	/**
	 * @generated
	 */
	private static final java.lang.String targetHomeName = "Districten";
	/**
	 * Create a link instance with the passed source bean.
	 * @generated
	 */
	public KieskringenToDistrictenLink(javax.ejb.EntityBean anEntityBean)
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
		.koaschema
		.DistrictenHome getTargetHome(
		com.ibm.ivj.ejb.associations.links.Link aLink)
		throws javax.naming.NamingException
	{
		if (targetHome == null)
			targetHome =
				(com
					.logicacmg
					.koa
					.koaschema
					.DistrictenHome) lookupTargetHome("java:comp/env/ejb/Districten",
					com.logicacmg.koa.koaschema.DistrictenHome.class);
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
					(com.logicacmg.koa.koaschema.DistrictenHome) getTargetHome(
						this)).findDistrictenByFk_dist_kkr(
					(com
						.logicacmg
						.koa
						.koaschema
						.KieskringenKey) getEntityContext()
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
		return ((com.logicacmg.koa.koaschema.KieskringenBean) source)
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
						.koaschema
						.Districten) anEJB)
						.secondarySetFk_dist_kkr(
				(com.logicacmg.koa.koaschema.Kieskringen) getEntityContext()
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
			((com.logicacmg.koa.koaschema.Districten) anEJB).setFk_dist_kkr(
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
						.koaschema
						.Districten) anEJB)
						.secondarySetFk_dist_kkr(
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
						.koaschema
						.Districten) targetEJB)
						.privateSetFk_dist_kkrKey(
				(com.logicacmg.koa.koaschema.KieskringenKey) getEntityContext()
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
			com.logicacmg.koa.koaschema.Districten.class);
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
				((com.logicacmg.koa.koaschema.Districten) anEJB)
					.getFk_dist_kkrKey());
	}
}
