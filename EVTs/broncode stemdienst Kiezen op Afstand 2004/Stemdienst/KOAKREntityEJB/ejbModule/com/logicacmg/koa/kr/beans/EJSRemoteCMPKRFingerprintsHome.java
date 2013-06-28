package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPKRFingerprintsHome
 * @generated
 */
public class EJSRemoteCMPKRFingerprintsHome extends EJSWrapper implements com.logicacmg.koa.kr.beans.KRFingerprintsHome {
	/**
	 * EJSRemoteCMPKRFingerprintsHome
	 * @generated
	 */
	public EJSRemoteCMPKRFingerprintsHome() throws java.rmi.RemoteException {
		super();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints create() throws javax.ejb.CreateException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = _EJS_beanRef.create();
		}
		catch (javax.ejb.CreateException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 0, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints create(java.math.BigDecimal xId, java.lang.Short xType, byte[] xFingerprint, java.sql.Timestamp xTimestamp, java.lang.String sSystemState) throws javax.ejb.CreateException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = _EJS_beanRef.create(xId, xType, xFingerprint, xTimestamp, sSystemState);
		}
		catch (javax.ejb.CreateException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 1, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByPrimaryKey(com.logicacmg.koa.kr.beans.KRFingerprintsKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = _EJS_beanRef.findByPrimaryKey(primaryKey);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 2, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * findByTypeAndState
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByTypeAndState(java.lang.Integer type, java.lang.String systemstatus) throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = _EJS_beanRef.findByTypeAndState(type, systemstatus);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 3, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * findLastDynamicFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastDynamicFP(java.lang.Integer type, java.lang.String firstState, java.lang.String secondState) throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = _EJS_beanRef.findLastDynamicFP(type, firstState, secondState);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 4, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * findLastFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastFP() throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 5, _EJS_s);
			_EJS_result = _EJS_beanRef.findLastFP();
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 5, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLatestFingerprint(java.lang.Integer type) throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 6, _EJS_s);
			_EJS_result = _EJS_beanRef.findLatestFingerprint(type);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 6, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getEJBMetaData
	 * @generated
	 */
	public javax.ejb.EJBMetaData getEJBMetaData() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		javax.ejb.EJBMetaData _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 7, _EJS_s);
			_EJS_result = _EJS_beanRef.getEJBMetaData();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 7, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getHomeHandle
	 * @generated
	 */
	public javax.ejb.HomeHandle getHomeHandle() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		javax.ejb.HomeHandle _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 8, _EJS_s);
			_EJS_result = _EJS_beanRef.getHomeHandle();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 8, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * remove
	 * @generated
	 */
	public void remove(java.lang.Object arg0) throws java.rmi.RemoteException, javax.ejb.RemoveException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 9, _EJS_s);
			_EJS_beanRef.remove(arg0);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (javax.ejb.RemoveException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 9, _EJS_s);
		}
		return ;
	}
	/**
	 * remove
	 * @generated
	 */
	public void remove(javax.ejb.Handle arg0) throws java.rmi.RemoteException, javax.ejb.RemoveException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.kr.beans.EJSCMPKRFingerprintsHomeBean)container.preInvoke(this, 10, _EJS_s);
			_EJS_beanRef.remove(arg0);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (javax.ejb.RemoveException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 10, _EJS_s);
		}
		return ;
	}
}
