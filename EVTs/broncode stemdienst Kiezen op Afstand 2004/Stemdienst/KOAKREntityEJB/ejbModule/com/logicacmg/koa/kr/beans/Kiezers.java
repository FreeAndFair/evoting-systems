package com.logicacmg.koa.kr.beans;
/**
 * Remote interface for Enterprise Bean: Kiezers
 */
public interface Kiezers extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: stemcode
	 */
	public java.lang.String getStemcode() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: stemcode
	 */
	public void setStemcode(java.lang.String newStemcode)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: kiezeridentificatie
	 */
	public java.lang.String getKiezeridentificatie()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: kiezeridentificatie
	 */
	public void setKiezeridentificatie(java.lang.String newKiezeridentificatie)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: hashedwachtwoord
	 */
	public java.lang.String getHashedwachtwoord()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: hashedwachtwoord
	 */
	public void setHashedwachtwoord(java.lang.String newHashedwachtwoord)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: districtnummer
	 */
	public java.lang.String getDistrictnummer()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: districtnummer
	 */
	public void setDistrictnummer(java.lang.String newDistrictnummer)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: kieskringnummer
	 */
	public java.lang.String getKieskringnummer()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: kieskringnummer
	 */
	public void setKieskringnummer(java.lang.String newKieskringnummer)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: reedsgestemd
	 */
	public java.lang.Boolean getReedsgestemd() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: reedsgestemd
	 */
	public void setReedsgestemd(java.lang.Boolean newReedsgestemd)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: invalidlogins
	 */
	public java.lang.Integer getInvalidlogins()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: invalidlogins
	 */
	public void setInvalidlogins(java.lang.Integer newInvalidlogins)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: loginattemptsleft
	 */
	public java.lang.Integer getLoginattemptsleft()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: loginattemptsleft
	 */
	public void setLoginattemptsleft(java.lang.Integer newLoginattemptsleft)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: timelastsuccesfullogin
	 */
	public java.sql.Timestamp getTimelastsuccesfullogin()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: timelastsuccesfullogin
	 */
	public void setTimelastsuccesfullogin(
		java.sql.Timestamp newTimelastsuccesfullogin)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: accountlocked
	 */
	public java.lang.Boolean getAccountlocked()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: accountlocked
	 */
	public void setAccountlocked(java.lang.Boolean newAccountlocked)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: timestampunlock
	 */
	public java.sql.Timestamp getTimestampunlock()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: timestampunlock
	 */
	public void setTimestampunlock(java.sql.Timestamp newTimestampunlock)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: verwijderd
	 */
	public java.lang.Boolean getVerwijderd() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: verwijderd
	 */
	public void setVerwijderd(java.lang.Boolean newVerwijderd)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: timestampvoted
	 */
	public java.lang.String getModaliteit() throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: timestampvoted
	 */
	public java.sql.Timestamp getTimestampGestemd()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: timestampvoted
	 */
	public void setModaliteit(java.lang.String newModaliteit)
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: timestampvoted
	 */
	public void setTimestampGestemd(java.sql.Timestamp newTimestampgestemd)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: transactienummer
	 */
	public java.lang.String getTransactienummer()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: transactienummer
	 */
	public void setTransactienummer(java.lang.String newTransactienummer)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: validlogins
	 */
	public java.lang.Integer getValidlogins() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: validlogins
	 */
	public void setValidlogins(java.lang.Integer newValidlogins)
		throws java.rmi.RemoteException;
}
