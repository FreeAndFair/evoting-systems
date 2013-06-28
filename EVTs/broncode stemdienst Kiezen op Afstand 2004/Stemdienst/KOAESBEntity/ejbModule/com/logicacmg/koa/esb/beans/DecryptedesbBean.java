package com.logicacmg.koa.esb.beans;
/**
 * Bean implementation class for Enterprise Bean: Decryptedesb
 */
public class DecryptedesbBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: stemnummer
	 */
	public java.math.BigDecimal stemnummer;
	/**
	 * Implemetation field for persistent attribute: kandidaatcode
	 */
	public java.lang.String kandidaatcode;
	/**
	 * Implemetation field for persistent attribute: kieskringnummer
	 */
	public java.lang.String kieskringnummer;
	/**
	 * Implemetation field for persistent attribute: districtnummer
	 */
	public java.lang.String districtnummer;
	/**
	 * Implemetation field for persistent attribute: kieslijstnummer
	 */
	public java.lang.String kieslijstnummer;
	/**
	 * Implemetation field for persistent attribute: positienummer
	 */
	public java.lang.String positienummer;
	/**
	 * Implemetation field for persistent attribute: lijstnaam
	 */
	public java.lang.String lijstnaam;
	/**
	 * Implemetation field for persistent attribute: kandidaatnaam
	 */
	public java.lang.String achternaam;
	/**
	 * Implemetation field for persistent attribute: voorletters
	 */
	public java.lang.String voorletters;
	/**
	 * Implemetation field for persistent attribute: kieskringnummer
	 */
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
	public com.logicacmg.koa.esb.beans.DecryptedesbKey ejbCreate(
		java.math.BigDecimal stemnummer)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.stemnummer = stemnummer;
		return null;
	}
	public com.logicacmg.koa.esb.beans.DecryptedesbKey ejbCreate(
		java.math.BigDecimal stemnummer,
		java.lang.String sKandidaatCode,
		java.lang.String sKieskringnummer,
		java.lang.String sDistrictnummer,
		java.lang.String sKieslijstnummer,
		java.lang.String sPositienummer,
		java.lang.String sLijstnaam,
		java.lang.String sAchternaam,
		java.lang.String sVoorletters)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.stemnummer = stemnummer;
		this.kandidaatcode = sKandidaatCode;
		this.kieskringnummer = sKieskringnummer;
		this.districtnummer = sDistrictnummer;
		this.kieslijstnummer = sKieslijstnummer;
		this.positienummer = sPositienummer;
		this.lijstnaam = sLijstnaam;
		this.achternaam = sAchternaam;
		this.voorletters = sVoorletters;
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
	public void ejbPostCreate(java.math.BigDecimal stemnummer)
		throws javax.ejb.CreateException
	{
	}
	public void ejbPostCreate(
		java.math.BigDecimal stemnummer,
		java.lang.String sKandidaatCode,
		java.lang.String sKieskringnummer,
		java.lang.String sDistrictnummer,
		java.lang.String sKieslijstnummer,
		java.lang.String sPositienummer,
		java.lang.String sLijstnaam,
		java.lang.String sAchternaam,
		java.lang.String sVoorletters)
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
	}
	/**
	 * This method was generated for supporting the associations.
	 */
	protected java.util.Vector _getLinks()
	{
		java.util.Vector links = new java.util.Vector();
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
	 * Get accessor for persistent attribute: kandidaatcode
	 */
	public java.lang.String getKandidaatcode()
	{
		return kandidaatcode;
	}
	/**
	 * Set accessor for persistent attribute: kandidaatcode
	 */
	public void setKandidaatcode(java.lang.String newKandidaatcode)
	{
		kandidaatcode = newKandidaatcode;
	}
	/**
	 * Get accessor for persistent attribute: kieskringnummer
	 */
	public java.lang.String getKieskringnummer()
	{
		return kieskringnummer;
	}
	/**
	 * Set accessor for persistent attribute: kieskringnummer
	 */
	public void setKieskringnummer(java.lang.String newKieskringnummer)
	{
		kieskringnummer = newKieskringnummer;
	}
	/**
	 * Get accessor for persistent attribute: districtnummer
	 */
	public java.lang.String getDistrictnummer()
	{
		return districtnummer;
	}
	/**
	 * Set accessor for persistent attribute: districtnummer
	 */
	public void setDistrictnummer(java.lang.String newDistrictnummer)
	{
		districtnummer = newDistrictnummer;
	}
	/**
	 * Get accessor for persistent attribute: kieslijstnummer
	 */
	public java.lang.String getKieslijstnummer()
	{
		return kieslijstnummer;
	}
	/**
	 * Set accessor for persistent attribute: kieslijstnummer
	 */
	public void setKieslijstnummer(java.lang.String newKieslijstnummer)
	{
		kieslijstnummer = newKieslijstnummer;
	}
	/**
	 * Get accessor for persistent attribute: positienummer
	 */
	public java.lang.String getPositienummer()
	{
		return positienummer;
	}
	/**
	 * Set accessor for persistent attribute: positienummer
	 */
	public void setPositienummer(java.lang.String newPositienummer)
	{
		positienummer = newPositienummer;
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
	 * Get accessor for persistent attribute: kandidaatnaam
	 */
	public java.lang.String getAchternaam()
	{
		return achternaam;
	}
	/**
	 * Set accessor for persistent attribute: kandidaatnaam
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
}
