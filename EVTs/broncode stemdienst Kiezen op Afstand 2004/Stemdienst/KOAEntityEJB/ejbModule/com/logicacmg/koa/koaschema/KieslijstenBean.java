package com.logicacmg.koa.koaschema;

import com.logicacmg.koa.koaschema.KieslijstenToFk_kkr_1Link;
import com.logicacmg.koa.koaschema.KieslijstenToLijstpositiesLink;

/**
 * Bean implementation class for Enterprise Bean: Kieslijsten
 */
public class KieslijstenBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: kieslijstnummer
	 */
	public java.lang.String kieslijstnummer;
	/**
	 * Implemetation field for persistent attribute: lijstnaam
	 */
	public java.lang.String lijstnaam;
	/**
	 * Implemetation field for persistent attribute: fk_kkr_1_kieskringnummer
	 */
	public java.lang.String fk_kkr_1_kieskringnummer;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink fk_kkr_1Link;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink lijstpositiesLink;
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
	public com.logicacmg.koa.koaschema.KieslijstenKey ejbCreate(
		java.lang.String kieslijstnummer,
		com.logicacmg.koa.koaschema.Kieskringen argFk_kkr_1)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.kieslijstnummer = kieslijstnummer;
		try
		{
			setFk_kkr_1(argFk_kkr_1);
		}
		catch (java.rmi.RemoteException remoteEx)
		{
			throw new javax.ejb.CreateException(remoteEx.getMessage());
		}
		return null;
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.koaschema.KieslijstenKey ejbCreate(
		java.lang.String kieslijstnummer,
		com.logicacmg.koa.koaschema.Kieskringen argFk_kkr_1,
		String lijstnaam)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.kieslijstnummer = kieslijstnummer;
		this.lijstnaam = lijstnaam;
		try
		{
			setFk_kkr_1(argFk_kkr_1);
		}
		catch (java.rmi.RemoteException remoteEx)
		{
			throw new javax.ejb.CreateException(remoteEx.getMessage());
		}
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
	public void ejbPostCreate(
		java.lang.String kieslijstnummer,
		com.logicacmg.koa.koaschema.Kieskringen argFk_kkr_1)
		throws javax.ejb.CreateException
	{
		try
		{
			setFk_kkr_1(argFk_kkr_1);
		}
		catch (java.rmi.RemoteException remoteEx)
		{
			throw new javax.ejb.CreateException(remoteEx.getMessage());
		}
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(
		java.lang.String kieslijstnummer,
		com.logicacmg.koa.koaschema.Kieskringen argFk_kkr_1,
		String lijstnaam)
		throws javax.ejb.CreateException
	{
		try
		{
			setFk_kkr_1(argFk_kkr_1);
		}
		catch (java.rmi.RemoteException remoteEx)
		{
			throw new javax.ejb.CreateException(remoteEx.getMessage());
		}
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
		lijstpositiesLink = null;
		fk_kkr_1Link = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		links.add(getLijstpositiesLink());
		links.add(getFk_kkr_1Link());
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
	 * Get accessor for persistent attribute: lijstnaam
	 */
	public java.lang.String getLijstnaam()
	{
		return lijstnaam;
	}
	/**
	 * Set accessor for persistent attribute: lijstnaam
	 */
	public void setLijstnaam(java.lang.String newLijstnaam)
	{
		lijstnaam = newLijstnaam;
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setFk_kkr_1(com.logicacmg.koa.koaschema.Kieskringen aFk_kkr_1)
		throws java.rmi.RemoteException
	{
		this.getFk_kkr_1Link().set(aFk_kkr_1);
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink getFk_kkr_1Link()
	{
		if (fk_kkr_1Link == null)
			fk_kkr_1Link = new KieslijstenToFk_kkr_1Link(this);
		return fk_kkr_1Link;
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey getFk_kkr_1Key()
	{
		com.logicacmg.koa.koaschema.KieskringenKey temp =
			new com.logicacmg.koa.koaschema.KieskringenKey();
		boolean fk_kkr_1_NULLTEST = true;
		fk_kkr_1_NULLTEST &= (fk_kkr_1_kieskringnummer == null);
		temp.kieskringnummer = fk_kkr_1_kieskringnummer;
		if (fk_kkr_1_NULLTEST)
			temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_kkr_1Key(
		com.logicacmg.koa.koaschema.KieskringenKey inKey)
	{
		boolean fk_kkr_1_NULLTEST = (inKey == null);
		fk_kkr_1_kieskringnummer =
			(fk_kkr_1_NULLTEST) ? null : inKey.kieskringnummer;
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Kieskringen getFk_kkr_1()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return (com.logicacmg.koa.koaschema.Kieskringen) this
			.getFk_kkr_1Link()
			.value();
	}
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddLijstposities(
		com.logicacmg.koa.koaschema.Lijstposities aLijstposities)
		throws java.rmi.RemoteException
	{
		this.getLijstpositiesLink().secondaryAddElement(aLijstposities);
	}
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveLijstposities(
		com.logicacmg.koa.koaschema.Lijstposities aLijstposities)
		throws java.rmi.RemoteException
	{
		this.getLijstpositiesLink().secondaryRemoveElement(aLijstposities);
	}
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink getLijstpositiesLink()
	{
		if (lijstpositiesLink == null)
			lijstpositiesLink = new KieslijstenToLijstpositiesLink(this);
		return lijstpositiesLink;
	}
	/**
	 * This method was generated for supporting the association named lijstposities.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getLijstposities()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return this.getLijstpositiesLink().enumerationValue();
	}
}
