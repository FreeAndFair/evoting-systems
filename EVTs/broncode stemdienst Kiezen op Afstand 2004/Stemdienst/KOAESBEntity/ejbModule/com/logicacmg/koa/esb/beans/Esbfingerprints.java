package com.logicacmg.koa.esb.beans;
/**
 * Remote interface for Enterprise Bean: Esbfingerprints
 */
public interface Esbfingerprints extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: fingerprint
	 */
	public byte[] getFingerprint() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: fingerprint
	 */
	public void setFingerprint(byte[] newFingerprint)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: timestamp
	 */
	public java.sql.Timestamp getTimestamp() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: timestamp
	 */
	public void setTimestamp(java.sql.Timestamp newTimestamp)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: systemstatus
	 */
	public java.lang.String getSystemstatus() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: systemstatus
	 */
	public void setSystemstatus(java.lang.String newSystemstatus)
		throws java.rmi.RemoteException;
}
