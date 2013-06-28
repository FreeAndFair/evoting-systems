package com.logicacmg.koa.kr.beans;
/**
 * Home interface for Enterprise Bean: KRFingerprints
 */
public interface KRFingerprintsHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: KRFingerprints
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Creates an instance from a key for Entity Bean: KRFingerprints
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints create(
		java.math.BigDecimal xId,
		Short xType,
		byte[] xFingerprint,
		java.sql.Timestamp xTimestamp,
		java.lang.String sSystemState)
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: KRFingerprints
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByPrimaryKey(
		com.logicacmg.koa.kr.beans.KRFingerprintsKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: KRFingerprints
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLatestFingerprint(
		java.lang.Integer type)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: KRFingerprints
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByTypeAndState(
		java.lang.Integer type,
		java.lang.String systemstatus)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: KRFingerprints
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastFP()
		throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * Finds the last created Dynamic Fingerprint instance in the blocked or the suspended state
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastDynamicFP(
		java.lang.Integer type,
		java.lang.String firstState,
		java.lang.String secondState)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
