package com.logicacmg.koa.kr.beans;
import com.logicacmg.koa.constants.FunctionalProps;
/**
 * Bean implementation class for Enterprise Bean: Kiezers
 */
public class KiezersBean implements javax.ejb.EntityBean
{
	private javax.ejb.EntityContext myEntityCtx;
	/**
	 * Implemetation field for persistent attribute: stemcode
	 */
	public java.lang.String stemcode;
	/**
	 * Implemetation field for persistent attribute: kiezeridentificatie
	 */
	public java.lang.String kiezeridentificatie;
	/**
	 * Implemetation field for persistent attribute: hashedwachtwoord
	 */
	public java.lang.String hashedwachtwoord;
	/**
	 * Implemetation field for persistent attribute: districtnummer
	 */
	public java.lang.String districtnummer;
	/**
	 * Implemetation field for persistent attribute: kieskringnummer
	 */
	public java.lang.String kieskringnummer;
	/**
	 * Implemetation field for persistent attribute: reedsgestemd
	 */
	public java.lang.Boolean reedsgestemd;
	/**
	 * Implemetation field for persistent attribute: invalidlogins
	 */
	public java.lang.Integer invalidlogins;
	/**
	 * Implemetation field for persistent attribute: loginattemptsleft
	 */
	public java.lang.Integer loginattemptsleft;
	/**
	 * Implemetation field for persistent attribute: timelastsuccesfullogin
	 */
	public java.sql.Timestamp timelastsuccesfullogin;
	/**
	 * Implemetation field for persistent attribute: accountlocked
	 */
	public java.lang.Boolean accountlocked;
	/**
	 * Implemetation field for persistent attribute: timestampunlock
	 */
	public java.sql.Timestamp timestampunlock;
	/**
	 * Implemetation field for persistent attribute: timestampvoted
	 */
	public java.sql.Timestamp timestampgestemd;
	/**
	 * Implemetation field for persistent attribute: modaliteit
	 */
	public java.lang.String modaliteit;
	/**
	 * Implemetation field for persistent attribute: verwijderd
	 */
	public java.lang.Boolean verwijderd;
	/**
	 * Implemetation field for persistent attribute: transactienummer
	 */
	public java.lang.String transactienummer;
	/**
	 * Implemetation field for persistent attribute: validlogins
	 */
	public java.lang.Integer validlogins;
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
	public com.logicacmg.koa.kr.beans.KiezersKey ejbCreate()
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.verwijderd = new Boolean(false);
		this.reedsgestemd = new Boolean(false);
		this.accountlocked = new Boolean(false);
		try
		{
			this.loginattemptsleft =
				new Integer(
					FunctionalProps.getIntProperty(
						FunctionalProps.LOGIN_NR_TIMES_LOGIN));
		}
		catch (Exception e)
		{
			this.loginattemptsleft = new Integer(3); // default value
		}
		return null;
	}
	public com.logicacmg.koa.kr.beans.KiezersKey ejbCreate(
		String sStemcode,
		String sKiezersidentificatie,
		String sHashedWachtwoord,
		String sDistrictnummer,
		String sKieskringnummer,
		String sTransactienummer)
		throws javax.ejb.CreateException
	{
		_initLinks();
		this.stemcode = sStemcode;
		this.kiezeridentificatie = sKiezersidentificatie;
		this.hashedwachtwoord = sHashedWachtwoord;
		this.districtnummer = sDistrictnummer;
		this.kieskringnummer = sKieskringnummer;
		this.transactienummer = sTransactienummer;
		this.verwijderd = new Boolean(false);
		this.reedsgestemd = new Boolean(false);
		this.accountlocked = new Boolean(false);
		try
		{
			this.loginattemptsleft =
				new Integer(
					FunctionalProps.getIntProperty(
						FunctionalProps.LOGIN_NR_TIMES_LOGIN));
		}
		catch (Exception e)
		{
			this.loginattemptsleft = new Integer(3); // default value
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
	public void ejbPostCreate() throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPostCreate
	 */
	public void ejbPostCreate(
		String sStemcode,
		String sKiezersidentificatie,
		String sHashedWachtwoord,
		String sDistrictnummer,
		String sKieskringnummer,
		String sTransactienummer)
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
	 * Get accessor for persistent attribute: stemcode
	 */
	public java.lang.String getStemcode()
	{
		return stemcode;
	}
	/**
	 * Set accessor for persistent attribute: stemcode
	 */
	public void setStemcode(java.lang.String newStemcode)
	{
		stemcode = newStemcode;
	}
	/**
	 * Get accessor for persistent attribute: kiezeridentificatie
	 */
	public java.lang.String getKiezeridentificatie()
	{
		return kiezeridentificatie;
	}
	/**
	 * Set accessor for persistent attribute: kiezeridentificatie
	 */
	public void setKiezeridentificatie(java.lang.String newKiezeridentificatie)
	{
		kiezeridentificatie = newKiezeridentificatie;
	}
	/**
	 * Get accessor for persistent attribute: hashedwachtwoord
	 */
	public java.lang.String getHashedwachtwoord()
	{
		return hashedwachtwoord;
	}
	/**
	 * Set accessor for persistent attribute: hashedwachtwoord
	 */
	public void setHashedwachtwoord(java.lang.String newHashedwachtwoord)
	{
		hashedwachtwoord = newHashedwachtwoord;
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
	 * Get accessor for persistent attribute: reedsgestemd
	 */
	public java.lang.Boolean getReedsgestemd()
	{
		return reedsgestemd;
	}
	/**
	 * Set accessor for persistent attribute: reedsgestemd
	 */
	public void setReedsgestemd(java.lang.Boolean newReedsgestemd)
	{
		reedsgestemd = newReedsgestemd;
	}
	/**
	 * Get accessor for persistent attribute: invalidlogins
	 */
	public java.lang.Integer getInvalidlogins()
	{
		return invalidlogins;
	}
	/**
	 * Set accessor for persistent attribute: invalidlogins
	 */
	public void setInvalidlogins(java.lang.Integer newInvalidlogins)
	{
		invalidlogins = newInvalidlogins;
	}
	/**
	 * Get accessor for persistent attribute: loginattemptsleft
	 */
	public java.lang.Integer getLoginattemptsleft()
	{
		return loginattemptsleft;
	}
	/**
	 * Set accessor for persistent attribute: loginattemptsleft
	 */
	public void setLoginattemptsleft(java.lang.Integer newLoginattemptsleft)
	{
		loginattemptsleft = newLoginattemptsleft;
	}
	/**
	 * Get accessor for persistent attribute: timelastsuccesfullogin
	 */
	public java.sql.Timestamp getTimelastsuccesfullogin()
	{
		return timelastsuccesfullogin;
	}
	/**
	 * Set accessor for persistent attribute: timelastsuccesfullogin
	 */
	public void setTimelastsuccesfullogin(
		java.sql.Timestamp newTimelastsuccesfullogin)
	{
		timelastsuccesfullogin = newTimelastsuccesfullogin;
	}
	/**
	 * Get accessor for persistent attribute: accountlocked
	 */
	public java.lang.Boolean getAccountlocked()
	{
		return accountlocked;
	}
	/**
	 * Set accessor for persistent attribute: accountlocked
	 */
	public void setAccountlocked(java.lang.Boolean newAccountlocked)
	{
		accountlocked = newAccountlocked;
	}
	/**
	 * Get accessor for persistent attribute: timestampunlock
	 */
	public java.sql.Timestamp getTimestampunlock()
	{
		return timestampunlock;
	}
	/**
	 * Set accessor for persistent attribute: timestampunlock
	 */
	public void setTimestampunlock(java.sql.Timestamp newTimestampunlock)
	{
		timestampunlock = newTimestampunlock;
	}
	/**
	 * Get accessor for persistent attribute: verwijderd
	 */
	public java.lang.Boolean getVerwijderd()
	{
		return verwijderd;
	}
	/**
	 * Set accessor for persistent attribute: verwijderd
	 */
	public void setVerwijderd(java.lang.Boolean newVerwijderd)
	{
		verwijderd = newVerwijderd;
	}
	/**
	 * Get accessor for persistent attribute: timestampvoted
	 */
	public java.sql.Timestamp getTimestampGestemd()
	{
		return timestampgestemd;
	}
	/**
	 * Set accessor for persistent attribute: timestampvoted
	 */
	public void setTimestampGestemd(java.sql.Timestamp newTimestampgestemd)
	{
		timestampgestemd = newTimestampgestemd;
	}
	/**
	 * Get accessor for persistent attribute: timestampvoted
	 */
	public java.lang.String getModaliteit()
	{
		return modaliteit;
	}
	/**
	 * Set accessor for persistent attribute: timestampvoted
	 */
	public void setModaliteit(java.lang.String newModaliteit)
	{
		modaliteit = newModaliteit;
	}
	/**
	 * Get accessor for persistent attribute: transactienummer
	 */
	public java.lang.String getTransactienummer()
	{
		return transactienummer;
	}
	/**
	 * Set accessor for persistent attribute: transactienummer
	 */
	public void setTransactienummer(java.lang.String newTransactienummer)
	{
		transactienummer = newTransactienummer;
	}
	/**
	 * Get accessor for persistent attribute: validlogins
	 */
	public java.lang.Integer getValidlogins()
	{
		return validlogins;
	}
	/**
	 * Set accessor for persistent attribute: validlogins
	 */
	public void setValidlogins(java.lang.Integer newValidlogins)
	{
		validlogins = newValidlogins;
	}
}
