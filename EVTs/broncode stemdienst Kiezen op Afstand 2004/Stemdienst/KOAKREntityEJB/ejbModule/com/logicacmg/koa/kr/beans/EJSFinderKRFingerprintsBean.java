package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderKRFingerprintsBean
 * @generated
 */
public interface EJSFinderKRFingerprintsBean {
	/**
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLatestFingerprint(java.lang.Integer type) throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * findLastDynamicFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastDynamicFP(java.lang.Integer type, java.lang.String firstState, java.lang.String secondState) throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * findByTypeAndState
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByTypeAndState(java.lang.Integer type, java.lang.String systemstatus) throws javax.ejb.FinderException, java.rmi.RemoteException;
	/**
	 * findLastFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastFP() throws javax.ejb.FinderException, java.rmi.RemoteException;
}
