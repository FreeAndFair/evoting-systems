package com.logicacmg.koa.koaschema;

import com.logicacmg.koa.koaschema.LijstpositiesToFk_klkr_1Link;
import com.logicacmg.koa.koaschema.LijstpositiesToKandidaatcodesLink;

/**
 * Bean implementation class for Enterprise Bean: Lijstposities
 */
public class LijstpositiesBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: positienummer
	 */
	public java.lang.String positienummer;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink kandidaatcodesLink;
	/**
	 * Implemetation field for persistent attribute: fk_klkr_1_kieslijstnummer
	 */
	public java.lang.String fk_klkr_1_kieslijstnummer;
	/**
	 * Implemetation field for persistent attribute: fk_klkr_1_fk_kkr_1_kieskringnummer
	 */
	public java.lang.String fk_klkr_1_fk_kkr_1_kieskringnummer;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink fk_klkr_1Link;
	/**
	 * Implemetation field for persistent attribute: achternaam
	 */
	public java.lang.String achternaam;
	/**
	 * Implemetation field for persistent attribute: voorletters
	 */
	public java.lang.String voorletters;
	/**
	 * Implemetation field for persistent attribute: roepnaam
	 */
	public java.lang.String roepnaam;
	/**
	 * Implemetation field for persistent attribute: geslacht
	 */
	public char geslacht;
	/**
	 * Implemetation field for persistent attribute: woonplaats
	 */
	public java.lang.String woonplaats;
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
	public com.logicacmg.koa.koaschema.LijstpositiesKey ejbCreate(
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1,
		String achternaam,
		String voorletters,
		String roepnaam,
		char geslacht,
		String woonplaats)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.positienummer = positienummer;
		this.achternaam = achternaam;
		this.voorletters = voorletters;
		this.roepnaam = roepnaam;
		this.geslacht = geslacht;
		this.woonplaats = woonplaats;
		try
		{
			setFk_klkr_1(argFk_klkr_1);
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
	public com.logicacmg.koa.koaschema.LijstpositiesKey ejbCreate(
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.positienummer = positienummer;
		this.achternaam = achternaam;
		try
		{
			setFk_klkr_1(argFk_klkr_1);
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
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1,
		String achternaam,
		String voorletters,
		String roepnaam,
		char geslacht,
		String woonplaats)
		throws javax.ejb.CreateException
	{
		try
		{
			setFk_klkr_1(argFk_klkr_1);
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
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1)
		throws javax.ejb.CreateException
	{
		try
		{
			setFk_klkr_1(argFk_klkr_1);
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
		kandidaatcodesLink = null;
		fk_klkr_1Link = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		links.add(getKandidaatcodesLink());
		links.add(getFk_klkr_1Link());
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
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException
	{
		this.getKandidaatcodesLink().secondaryAddElement(aKandidaatcodes);
	}
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException
	{
		this.getKandidaatcodesLink().secondaryRemoveElement(aKandidaatcodes);
	}
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.ManyLink getKandidaatcodesLink()
	{
		if (kandidaatcodesLink == null)
			kandidaatcodesLink = new LijstpositiesToKandidaatcodesLink(this);
		return kandidaatcodesLink;
	}
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getKandidaatcodes()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return this.getKandidaatcodesLink().enumerationValue();
	}
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void addKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException
	{
		this.getKandidaatcodesLink().addElement(aKandidaatcodes);
	}
	/**
	 * This method was generated for supporting the association named kandidaatcodes.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void removeKandidaatcodes(
		com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes)
		throws java.rmi.RemoteException
	{
		this.getKandidaatcodesLink().removeElement(aKandidaatcodes);
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setFk_klkr_1(
		com.logicacmg.koa.koaschema.Kieslijsten aFk_klkr_1)
		throws java.rmi.RemoteException
	{
		this.getFk_klkr_1Link().set(aFk_klkr_1);
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink getFk_klkr_1Link()
	{
		if (fk_klkr_1Link == null)
			fk_klkr_1Link = new LijstpositiesToFk_klkr_1Link(this);
		return fk_klkr_1Link;
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieslijstenKey getFk_klkr_1Key()
	{
		com.logicacmg.koa.koaschema.KieslijstenKey temp =
			new com.logicacmg.koa.koaschema.KieslijstenKey();
		boolean fk_klkr_1_NULLTEST = true;
		fk_klkr_1_NULLTEST &= (fk_klkr_1_kieslijstnummer == null);
		temp.kieslijstnummer = fk_klkr_1_kieslijstnummer;
		fk_klkr_1_NULLTEST &= (fk_klkr_1_fk_kkr_1_kieskringnummer == null);
		temp.fk_kkr_1_kieskringnummer = fk_klkr_1_fk_kkr_1_kieskringnummer;
		if (fk_klkr_1_NULLTEST)
			temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_klkr_1Key(
		com.logicacmg.koa.koaschema.KieslijstenKey inKey)
	{
		boolean fk_klkr_1_NULLTEST = (inKey == null);
		fk_klkr_1_kieslijstnummer =
			(fk_klkr_1_NULLTEST) ? null : inKey.kieslijstnummer;
		fk_klkr_1_fk_kkr_1_kieskringnummer =
			(fk_klkr_1_NULLTEST) ? null : inKey.fk_kkr_1_kieskringnummer;
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Kieslijsten getFk_klkr_1()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return (com.logicacmg.koa.koaschema.Kieslijsten) this
			.getFk_klkr_1Link()
			.value();
	}
	/**
	 * Get accessor for persistent attribute: achternaam
	 */
	public java.lang.String getAchternaam()
	{
		return achternaam;
	}
	/**
	 * Set accessor for persistent attribute: achternaam
	 */
	public void setAchternaam(java.lang.String newAchternaam)
	{
		achternaam = newAchternaam;
	}
	/**
	 * Get accessor for persistent attribute: voorletters
	 */
	public java.lang.String getVoorletters()
	{
		return voorletters;
	}
	/**
	 * Set accessor for persistent attribute: voorletters
	 */
	public void setVoorletters(java.lang.String newVoorletters)
	{
		voorletters = newVoorletters;
	}
	/**
	 * Get accessor for persistent attribute: roepnaam
	 */
	public java.lang.String getRoepnaam()
	{
		return roepnaam;
	}
	/**
	 * Set accessor for persistent attribute: roepnaam
	 */
	public void setRoepnaam(java.lang.String newRoepnaam)
	{
		roepnaam = newRoepnaam;
	}
	/**
	 * Get accessor for persistent attribute: geslacht
	 */
	public char getGeslacht()
	{
		return geslacht;
	}
	/**
	 * Set accessor for persistent attribute: geslacht
	 */
	public void setGeslacht(char newGeslacht)
	{
		geslacht = newGeslacht;
	}
	/**
	 * Get accessor for persistent attribute: woonplaats
	 */
	public java.lang.String getWoonplaats()
	{
		return woonplaats;
	}
	/**
	 * Set accessor for persistent attribute: woonplaats
	 */
	public void setWoonplaats(java.lang.String newWoonplaats)
	{
		woonplaats = newWoonplaats;
	}
}
