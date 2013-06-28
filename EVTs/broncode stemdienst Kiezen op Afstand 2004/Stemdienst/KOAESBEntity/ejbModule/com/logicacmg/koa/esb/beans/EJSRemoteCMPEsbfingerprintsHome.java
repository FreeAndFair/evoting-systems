package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPEsbfingerprintsHome
 * @generated
 */
public class EJSRemoteCMPEsbfingerprintsHome extends EJSWrapper implements com.logicacmg.koa.esb.beans.EsbfingerprintsHome {
	/**
	 * EJSRemoteCMPEsbfingerprintsHome
	 * @generated
	 */
	public EJSRemoteCMPEsbfingerprintsHome() throws java.rmi.RemoteException {
		super();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints create(java.math.BigDecimal id) throws javax.ejb.CreateException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.esb.beans.Esbfingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = _EJS_beanRef.create(id);
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
	public com.logicacmg.koa.esb.beans.Esbfingerprints create(java.math.BigDecimal id, byte[] xFingerprint, java.sql.Timestamp xTimestamp, java.lang.String sSystemState) throws javax.ejb.CreateException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.esb.beans.Esbfingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = _EJS_beanRef.create(id, xFingerprint, xTimestamp, sSystemState);
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
	public com.logicacmg.koa.esb.beans.Esbfingerprints findByPrimaryKey(com.logicacmg.koa.esb.beans.EsbfingerprintsKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.esb.beans.Esbfingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 2, _EJS_s);
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
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints findLatestFingerprint() throws javax.ejb.FinderException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.esb.beans.Esbfingerprints _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = _EJS_beanRef.findLatestFingerprint();
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
	 * getEJBMetaData
	 * @generated
	 */
	public javax.ejb.EJBMetaData getEJBMetaData() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		javax.ejb.EJBMetaData _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 4, _EJS_s);
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
			container.postInvoke(this, 4, _EJS_s);
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
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 5, _EJS_s);
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
			container.postInvoke(this, 5, _EJS_s);
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
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 6, _EJS_s);
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
			container.postInvoke(this, 6, _EJS_s);
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
			com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean _EJS_beanRef = (com.logicacmg.koa.esb.beans.EJSCMPEsbfingerprintsHomeBean)container.preInvoke(this, 7, _EJS_s);
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
			container.postInvoke(this, 7, _EJS_s);
		}
		return ;
	}
}
