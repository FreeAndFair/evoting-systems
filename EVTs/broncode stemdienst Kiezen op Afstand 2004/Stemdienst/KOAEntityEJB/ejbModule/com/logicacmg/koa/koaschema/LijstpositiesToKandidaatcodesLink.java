package com.logicacmg.koa.koaschema;
import java.util.Enumeration;

import javax.naming.NamingException;
/**
 * LijstpositiesToKandidaatcodesLink
 * @generated
 */
public class LijstpositiesToKandidaatcodesLink
	extends com.ibm.ivj.ejb.associations.links.SingleToManyLink
{
	/**
	 * @generated
	 */
	private static com.logicacmg.koa.koaschema.KandidaatcodesHome targetHome;
	/**
	 * @generated
	 */
	private static final java.lang.String targetHomeName = "Kandidaatcodes";
	/**
	 * Create a link instance with the passed source bean.
	 * @generated
	 */
	public LijstpositiesToKandidaatcodesLink(javax.ejb.EntityBean anEntityBean)
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
		.KandidaatcodesHome getTargetHome(
			com.ibm.ivj.ejb.associations.links.Link aLink)
		throws javax.naming.NamingException
	{
		if (targetHome == null)
			targetHome =
				(com
					.logicacmg
					.koa
					.koaschema
					.KandidaatcodesHome) lookupTargetHome("java:comp/env/ejb/Kandidaatcodes",
					com.logicacmg.koa.koaschema.KandidaatcodesHome.class);
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
						.koaschema
						.KandidaatcodesHome) getTargetHome(
						this)).findKandidaatcodesByFk_kkrklpn_1(
					(com
						.logicacmg
						.koa
						.koaschema
						.LijstpositiesKey) getEntityContext()
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
		return ((com.logicacmg.koa.koaschema.LijstpositiesBean) source)
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
						.Kandidaatcodes) anEJB)
						.secondarySetFk_kkrklpn_1(
				(com.logicacmg.koa.koaschema.Lijstposities) getEntityContext()
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
						.koaschema
						.Kandidaatcodes) anEJB)
						.setFk_kkrklpn_1(
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
						.Kandidaatcodes) anEJB)
						.secondarySetFk_kkrklpn_1(
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
						.Kandidaatcodes) targetEJB)
						.privateSetFk_kkrklpn_1Key(
				(com
					.logicacmg
					.koa
					.koaschema
					.LijstpositiesKey) getEntityContext()
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
			com.logicacmg.koa.koaschema.Kandidaatcodes.class);
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
				((com.logicacmg.koa.koaschema.Kandidaatcodes) anEJB)
					.getFk_kkrklpn_1Key());
	}
}
