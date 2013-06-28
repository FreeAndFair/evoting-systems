package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessESBSessionEJB
 * @generated
 */
public class EJSRemoteStatelessESBSessionEJB extends EJSWrapper implements ESBSessionEJB {
	/**
	 * EJSRemoteStatelessESBSessionEJB
	 * @generated
	 */
	public EJSRemoteStatelessESBSessionEJB() throws java.rmi.RemoteException {
		super();	}
	/**
	 * collectCounters
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CounterData collectCounters(java.lang.String sComponentID) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CounterData _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.ESBSessionEJBBean beanRef = (com.logicacmg.koa.esb.beans.ESBSessionEJBBean)container.preInvoke(this, 0, _EJS_s);
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
	 * changeState
	 * @generated
	 */
	public void changeState(java.lang.String sCurrentState, java.lang.String sNewState) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.esb.beans.ESBSessionEJBBean beanRef = (com.logicacmg.koa.esb.beans.ESBSessionEJBBean)container.preInvoke(this, 1, _EJS_s);
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
			container.postInvoke(this, 1, _EJS_s);
		}
		return ;
	}
	/**
	 * emptyESB
	 * @generated
	 */
	public void emptyESB() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.esb.beans.ESBSessionEJBBean beanRef = (com.logicacmg.koa.esb.beans.ESBSessionEJBBean)container.preInvoke(this, 2, _EJS_s);
			beanRef.emptyESB();
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
		return ;
	}
	/**
	 * openESB
	 * @generated
	 */
	public void openESB(byte[] baPrivateKey, java.lang.String sPassword) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.esb.beans.ESBSessionEJBBean beanRef = (com.logicacmg.koa.esb.beans.ESBSessionEJBBean)container.preInvoke(this, 3, _EJS_s);
			beanRef.openESB(baPrivateKey, sPassword);
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
		return ;
	}
	/**
	 * saveEncryptedVote
	 * @generated
	 */
	public void saveEncryptedVote(com.logicacmg.koa.dataobjects.EncryptedStem xEncryptedStem) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.esb.beans.ESBSessionEJBBean beanRef = (com.logicacmg.koa.esb.beans.ESBSessionEJBBean)container.preInvoke(this, 4, _EJS_s);
			beanRef.saveEncryptedVote(xEncryptedStem);
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
			container.postInvoke(this, 4, _EJS_s);
		}
		return ;
	}
	/**
	 * telStemmen
	 * @generated
	 */
	public void telStemmen() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.esb.beans.ESBSessionEJBBean beanRef = (com.logicacmg.koa.esb.beans.ESBSessionEJBBean)container.preInvoke(this, 5, _EJS_s);
			beanRef.telStemmen();
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
}
