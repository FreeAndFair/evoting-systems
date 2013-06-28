package com.logicacmg.koa.koaschema;
import javax.naming.NamingException;
/**
 * KieslijstenToFk_kkr_1Link
 * @generated
 */
public class KieslijstenToFk_kkr_1Link
	extends com.ibm.ivj.ejb.associations.links.ManyToSingleLink
{
	/**
	 * @generated
	 */
	private static com.logicacmg.koa.koaschema.KieskringenHome targetHome;
	/**
	 * @generated
	 */
	private static final java.lang.String targetHomeName = "Kieskringen";
	/**
	 * Create a link instance with the passed source bean.
	 * @generated
	 */
	public KieslijstenToFk_kkr_1Link(javax.ejb.EntityBean anEntityBean)
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
		.KieskringenHome getTargetHome(
			com.ibm.ivj.ejb.associations.links.Link aLink)
		throws javax.naming.NamingException
	{
		if (targetHome == null)
			targetHome =
				(com
					.logicacmg
					.koa
					.koaschema
					.KieskringenHome) lookupTargetHome("java:comp/env/ejb/Kieskringen",
					com.logicacmg.koa.koaschema.KieskringenHome.class);
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
		com.logicacmg.koa.koaschema.KieskringenKey key =
			((com.logicacmg.koa.koaschema.KieslijstenBean) source)
				.getFk_kkr_1Key();
		try
		{
			target =
				(
					(com
						.logicacmg
						.koa
						.koaschema
						.KieskringenHome) getTargetHome(
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
		return ((com.logicacmg.koa.koaschema.KieslijstenBean) source)
			.getEntityContext();
	}
	/**
	 * Return whether or not the source key is valid for querying.
	 * @generated
	 */
	protected boolean isKeyValid()
	{
		return (
			((com.logicacmg.koa.koaschema.KieslijstenBean) source)
				.getFk_kkr_1Key()
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
						.koaschema
						.Kieskringen) anEJB)
						.secondaryRemoveKieslijsten(
				(com.logicacmg.koa.koaschema.Kieslijsten) getEntityContext()
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
						.koaschema
						.Kieskringen) anEJB)
						.secondaryAddKieslijsten(
				(com.logicacmg.koa.koaschema.Kieslijsten) getEntityContext()
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
						.koaschema
						.KieslijstenBean) source)
						.privateSetFk_kkr_1Key(
				null);
		else
			(
				(
					com
						.logicacmg
						.koa
						.koaschema
						.KieslijstenBean) source)
						.privateSetFk_kkr_1Key(
				(com.logicacmg.koa.koaschema.KieskringenKey) targetEJB
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
					.koaschema
					.KieslijstenBean) source)
					.privateSetFk_kkr_1Key(
			null);
	}
}
