package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessKRSessionEJB
 * @generated
 */
public class EJSRemoteStatelessKRSessionEJB extends EJSWrapper implements KRSessionEJB {
	/**
	 * EJSRemoteStatelessKRSessionEJB
	 * @generated
	 */
	public EJSRemoteStatelessKRSessionEJB() throws java.rmi.RemoteException {
		super();	}
	/**
	 * collectCounters
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CounterData collectCounters(java.lang.String sComponentID) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CounterData _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.collectCounters(sComponentID);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
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
	 * getKiezer
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.Kiezer getKiezer(java.lang.String sStemcode) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.Kiezer _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getKiezer(sStemcode);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
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
	 * verifyKiezer
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.StemTransactie verifyKiezer(java.lang.String sStemcode, java.lang.String sWachtwoord, java.lang.String sModaliteit, boolean bUpdateCounters) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.StemTransactie _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.verifyKiezer(sStemcode, sWachtwoord, sModaliteit, bUpdateCounters);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
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
	 * getCurrentSystemState
	 * @generated
	 */
	public java.lang.String getCurrentSystemState() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.getCurrentSystemState();
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
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
	 * changeState
	 * @generated
	 */
	public void changeState(java.lang.String sCurrentState, java.lang.String sNewState) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 4, _EJS_s);
			beanRef.changeState(sCurrentState, sNewState);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
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
	 * emptyKR
	 * @generated
	 */
	public void emptyKR() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 5, _EJS_s);
			beanRef.emptyKR();
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
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
		return ;
	}
	/**
	 * kiezerHeeftGestemd
	 * @generated
	 */
	public void kiezerHeeftGestemd(com.logicacmg.koa.dataobjects.Kiezer xKiezer) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KRSessionEJBBean beanRef = (com.logicacmg.koa.kr.beans.KRSessionEJBBean)container.preInvoke(this, 6, _EJS_s);
			beanRef.kiezerHeeftGestemd(xKiezer);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
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
		return ;
	}
}
