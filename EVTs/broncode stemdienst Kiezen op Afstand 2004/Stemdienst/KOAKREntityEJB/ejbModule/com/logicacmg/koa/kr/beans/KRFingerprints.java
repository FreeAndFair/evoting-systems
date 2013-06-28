package com.logicacmg.koa.kr.beans;
/**
 * Remote interface for Enterprise Bean: KRFingerprints
 */
public interface KRFingerprints extends javax.ejb.EJBObject
{
	public byte[] getFingerprint() throws java.rmi.RemoteException;
	public void setFingerprint(byte[] newFingerprint)
		throws java.rmi.RemoteException;
	public java.sql.Timestamp getTimestamp() throws java.rmi.RemoteException;
	public void setTimestamp(java.sql.Timestamp newTimestamp)
		throws java.rmi.RemoteException;
	public java.lang.String getSystemstatus() throws java.rmi.RemoteException;
	public void setSystemstatus(java.lang.String newSystemstatus)
		throws java.rmi.RemoteException;
}
