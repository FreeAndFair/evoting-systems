package com.logicacmg.koa.koaschema;

import com.logicacmg.koa.koaschema.KandidaatcodesToFk_kkrklpn_1Link;

/**
 * Bean implementation class for Enterprise Bean: Kandidaatcodes
 */
public class KandidaatcodesBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: kandidaatcode
	 */
	public java.lang.String kandidaatcode;
	/**
	 * Implemetation field for persistent attribute: fk_kkrklpn_1_positienummer
	 */
	public java.lang.String fk_kkrklpn_1_positienummer;
	/**
	 * Implemetation field for persistent attribute: fk_kkrklpn_1_fk_klkr_1_kieslijstnummer
	 */
	public java.lang.String fk_kkrklpn_1_fk_klkr_1_kieslijstnummer;
	/**
	 * Implemetation field for persistent attribute: fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer
	 */
	public java.lang.String fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer;
	private transient com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink fk_kkrklpn_1Link;
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
	public com.logicacmg.koa.koaschema.KandidaatcodesKey ejbCreate(
		java.lang.String kandidaatcode)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.kandidaatcode = kandidaatcode;
		return null;
	}
	/**
	 * ejbCreate method for a CMP entity bean.
	 */
	public com.logicacmg.koa.koaschema.KandidaatcodesKey ejbCreate(
		String kandidaatcode,
		String positienummer,
		String kieslijstnummer,
		String kieskringnummer)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.kandidaatcode = kandidaatcode;
		this.fk_kkrklpn_1_positienummer = positienummer;
		this.fk_kkrklpn_1_fk_klkr_1_kieslijstnummer = kieslijstnummer;
		this.fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer = kieskringnummer;
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
	public void ejbPostCreate(java.lang.String kandidaatcode)
		throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(
		String kandidaatcode,
		String positienummer,
		String kieslijstnummer,
		String kieskringnummer)
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
		fk_kkrklpn_1Link = null;
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
		links.add(getFk_kkrklpn_1Link());
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
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setFk_kkrklpn_1(
		com.logicacmg.koa.koaschema.Lijstposities aFk_kkrklpn_1)
		throws java.rmi.RemoteException
	{
		this.getFk_kkrklpn_1Link().set(aFk_kkrklpn_1);
	}
	/**
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondarySetFk_kkrklpn_1(
		com.logicacmg.koa.koaschema.Lijstposities aFk_kkrklpn_1)
		throws java.rmi.RemoteException
	{
		this.getFk_kkrklpn_1Link().secondarySet(aFk_kkrklpn_1);
	}
	/**
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	protected com
		.ibm
		.ivj
		.ejb
		.associations
		.interfaces
		.SingleLink getFk_kkrklpn_1Link()
	{
		if (fk_kkrklpn_1Link == null)
			fk_kkrklpn_1Link = new KandidaatcodesToFk_kkrklpn_1Link(this);
		return fk_kkrklpn_1Link;
	}
	/**
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.LijstpositiesKey getFk_kkrklpn_1Key()
	{
		com.logicacmg.koa.koaschema.LijstpositiesKey temp =
			new com.logicacmg.koa.koaschema.LijstpositiesKey();
		boolean fk_kkrklpn_1_NULLTEST = true;
		fk_kkrklpn_1_NULLTEST &= (fk_kkrklpn_1_positienummer == null);
		temp.positienummer = fk_kkrklpn_1_positienummer;
		fk_kkrklpn_1_NULLTEST
			&= (fk_kkrklpn_1_fk_klkr_1_kieslijstnummer == null);
		temp.fk_klkr_1_kieslijstnummer = fk_kkrklpn_1_fk_klkr_1_kieslijstnummer;
		fk_kkrklpn_1_NULLTEST
			&= (fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer == null);
		temp.fk_klkr_1_fk_kkr_1_kieskringnummer =
			fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer;
		if (fk_kkrklpn_1_NULLTEST)
			temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_kkrklpn_1Key(
		com.logicacmg.koa.koaschema.LijstpositiesKey inKey)
	{
		boolean fk_kkrklpn_1_NULLTEST = (inKey == null);
		fk_kkrklpn_1_positienummer =
			(fk_kkrklpn_1_NULLTEST) ? null : inKey.positienummer;
		fk_kkrklpn_1_fk_klkr_1_kieslijstnummer =
			(fk_kkrklpn_1_NULLTEST) ? null : inKey.fk_klkr_1_kieslijstnummer;
		fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer =
			(fk_kkrklpn_1_NULLTEST)
				? null
				: inKey.fk_klkr_1_fk_kkr_1_kieskringnummer;
	}
	/**
	 * This method was generated for supporting the association named fk_kkrklpn_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.Lijstposities getFk_kkrklpn_1()
		throws java.rmi.RemoteException, javax.ejb.FinderException
	{
		return (com.logicacmg.koa.koaschema.Lijstposities) this
			.getFk_kkrklpn_1Link()
			.value();
	}
}
