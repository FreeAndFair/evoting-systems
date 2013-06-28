package com.logicacmg.koa.koaschema;

import com.logicacmg.koa.koaschema.KieskringenToDistrictenLink;
import com.logicacmg.koa.koaschema.KieskringenToKieslijstenLink;

/**
 * Bean implementation class for Enterprise Bean: Kieskringen
 */
public class KieskringenBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: kieskringnummer
	 */
	public java.lang.String kieskringnummer;
	/**
	 * Implemetation field for persistent attribute: kieskringnaam
	 */
	public java.lang.String kieskringnaam;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink districtenLink;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink kieslijstenLink;
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
	public com.logicacmg.koa.koaschema.KieskringenKey ejbCreate(
		java.lang.String kieskringnummer)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.kieskringnummer = kieskringnummer;
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
	public void ejbPostCreate(java.lang.String kieskringnummer)
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
		kieslijstenLink = null;
		districtenLink = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		links.add(getKieslijstenLink());
		links.add(getDistrictenLink());
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
	 * Get accessor for persistent attribute: kieskringnaam
	 */
	public java.lang.String getKieskringnaam()
	{
		return kieskringnaam;
	}
	/**
	 * Set accessor for persistent attribute: kieskringnaam
	 */
	public void setKieskringnaam(java.lang.String newKieskringnaam)
	{
		kieskringnaam = newKieskringnaam;
	}
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException
	{
		this.getDistrictenLink().secondaryAddElement(aDistricten);
	}
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException
	{
		this.getDistrictenLink().secondaryRemoveElement(aDistricten);
	}
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink getDistrictenLink()
	{
		if (districtenLink == null)
			districtenLink = new KieskringenToDistrictenLink(this);
		return districtenLink;
	}
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getDistricten()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return this.getDistrictenLink().enumerationValue();
	}
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void addDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException
	{
		this.getDistrictenLink().addElement(aDistricten);
	}
	/**
	 * This method was generated for supporting the association named districten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void removeDistricten(
		com.logicacmg.koa.koaschema.Districten aDistricten)
		throws java.rmi.RemoteException
	{
		this.getDistrictenLink().removeElement(aDistricten);
	}
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddKieslijsten(
		com.logicacmg.koa.koaschema.Kieslijsten aKieslijsten)
		throws java.rmi.RemoteException
	{
		this.getKieslijstenLink().secondaryAddElement(aKieslijsten);
	}
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveKieslijsten(
		com.logicacmg.koa.koaschema.Kieslijsten aKieslijsten)
		throws java.rmi.RemoteException
	{
		this.getKieslijstenLink().secondaryRemoveElement(aKieslijsten);
	}
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink getKieslijstenLink()
	{
		if (kieslijstenLink == null)
			kieslijstenLink = new KieskringenToKieslijstenLink(this);
		return kieslijstenLink;
	}
	/**
	 * This method was generated for supporting the association named kieslijsten.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getKieslijsten()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return this.getKieslijstenLink().enumerationValue();
	}
}
