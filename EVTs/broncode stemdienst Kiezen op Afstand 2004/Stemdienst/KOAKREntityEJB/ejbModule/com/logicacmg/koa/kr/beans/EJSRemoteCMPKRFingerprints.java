package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPKRFingerprints
 * @generated
 */
public class EJSRemoteCMPKRFingerprints extends EJSWrapper implements KRFingerprints {
	/**
	 * EJSRemoteCMPKRFingerprints
	 * @generated
	 */
	public EJSRemoteCMPKRFingerprints() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getFingerprint
	 * @generated
	 */
	public byte[] getFingerprint() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		byte[] _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRFingerprintsBean beanRef = (com.logicacmg.koa.kr.beans.KRFingerprintsBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getFingerprint();
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
	 * getSystemstatus
	 * @generated
	 */
	public java.lang.String getSystemstatus() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRFingerprintsBean beanRef = (com.logicacmg.koa.kr.beans.KRFingerprintsBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getSystemstatus();
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
	 * getTimestamp
	 * @generated
	 */
	public java.sql.Timestamp getTimestamp() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRFingerprintsBean beanRef = (com.logicacmg.koa.kr.beans.KRFingerprintsBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.getTimestamp();
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
	 * setFingerprint
	 * @generated
	 */
	public void setFingerprint(byte[] newFingerprint) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KRFingerprintsBean beanRef = (com.logicacmg.koa.kr.beans.KRFingerprintsBean)container.preInvoke(this, 3, _EJS_s);
			beanRef.setFingerprint(newFingerprint);
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
		return ;
	}
	/**
	 * setSystemstatus
	 * @generated
	 */
	public void setSystemstatus(java.lang.String newSystemstatus) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KRFingerprintsBean beanRef = (com.logicacmg.koa.kr.beans.KRFingerprintsBean)container.preInvoke(this, 4, _EJS_s);
			beanRef.setSystemstatus(newSystemstatus);
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
		return ;
	}
	/**
	 * setTimestamp
	 * @generated
	 */
	public void setTimestamp(java.sql.Timestamp newTimestamp) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KRFingerprintsBean beanRef = (com.logicacmg.koa.kr.beans.KRFingerprintsBean)container.preInvoke(this, 5, _EJS_s);
			beanRef.setTimestamp(newTimestamp);
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
		return ;
	}
}
