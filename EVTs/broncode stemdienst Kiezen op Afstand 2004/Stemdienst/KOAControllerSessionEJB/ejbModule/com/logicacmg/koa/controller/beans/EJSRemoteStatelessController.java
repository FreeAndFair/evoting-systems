package com.logicacmg.koa.controller.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessController
 * @generated
 */
public class EJSRemoteStatelessController extends EJSWrapper implements Controller {
	/**
	 * EJSRemoteStatelessController
	 * @generated
	 */
	public EJSRemoteStatelessController() throws java.rmi.RemoteException {
		super();	}
	/**
	 * checkPinCode
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult checkPinCode(java.lang.String sPincode1, java.lang.String sPincode2) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.checkPinCode(sPincode1, sPincode2);
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
	 * close
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult close() throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.close();
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
		return _EJS_result;
	}
	/**
	 * countVote
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult countVote() throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.countVote();
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
			container.postInvoke(this, 2, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * initialize
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult initialize(java.security.PublicKey pkPublicKey) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.initialize(pkPublicKey);
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
			container.postInvoke(this, 3, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * open
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult open() throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = beanRef.open();
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
		return _EJS_result;
	}
	/**
	 * prepare
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult prepare() throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 5, _EJS_s);
			_EJS_result = beanRef.prepare();
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
			container.postInvoke(this, 5, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * prepareVoteCount
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult prepareVoteCount(byte[] baPrivateKey, java.lang.String sPassword) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 6, _EJS_s);
			_EJS_result = beanRef.prepareVoteCount(baPrivateKey, sPassword);
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
			container.postInvoke(this, 6, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * reInitialize
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult reInitialize(java.security.PublicKey pkPublicKey) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 7, _EJS_s);
			_EJS_result = beanRef.reInitialize(pkPublicKey);
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
			container.postInvoke(this, 7, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * suspend
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.CallResult suspend() throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.CallResult _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 8, _EJS_s);
			_EJS_result = beanRef.suspend();
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
			container.postInvoke(this, 8, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getNextSequenceNumber
	 * @generated
	 */
	public int getNextSequenceNumber() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		int _EJS_result = 0;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 9, _EJS_s);
			_EJS_result = beanRef.getNextSequenceNumber();
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
			container.postInvoke(this, 9, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getCurrentState
	 * @generated
	 */
	public java.lang.String getCurrentState() throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 10, _EJS_s);
			_EJS_result = beanRef.getCurrentState();
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
			container.postInvoke(this, 10, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * requestSubscription
	 * @generated
	 */
	public java.lang.String requestSubscription(java.lang.String sComponentType) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 11, _EJS_s);
			_EJS_result = beanRef.requestSubscription(sComponentType);
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
			container.postInvoke(this, 11, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * subscriptionComplete
	 * @generated
	 */
	public java.lang.String subscriptionComplete(com.logicacmg.koa.controller.subscription.ClientSubscription xClient) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 12, _EJS_s);
			_EJS_result = beanRef.subscriptionComplete(xClient);
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
			container.postInvoke(this, 12, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getPublicKey
	 * @generated
	 */
	public java.security.PublicKey getPublicKey() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.security.PublicKey _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 13, _EJS_s);
			_EJS_result = beanRef.getPublicKey();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 13, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getAvailableStates
	 * @generated
	 */
	public java.util.Vector getAvailableStates(java.lang.String sCurrentState) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Vector _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 14, _EJS_s);
			_EJS_result = beanRef.getAvailableStates(sCurrentState);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 14, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getCurrentCounters
	 * @generated
	 */
	public java.util.Vector getCurrentCounters() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Vector _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 15, _EJS_s);
			_EJS_result = beanRef.getCurrentCounters();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 15, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * block
	 * @generated
	 */
	public void block() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 16, _EJS_s);
			beanRef.block();
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
			container.postInvoke(this, 16, _EJS_s);
		}
		return ;
	}
	/**
	 * collectCounters
	 * @generated
	 */
	public void collectCounters(java.lang.String sInitiationAction, int timing) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 17, _EJS_s);
			beanRef.collectCounters(sInitiationAction, timing);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 17, _EJS_s);
		}
		return ;
	}
	/**
	 * unsubscribe
	 * @generated
	 */
	public void unsubscribe(java.lang.String sComponentID) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.controller.beans.ControllerBean beanRef = (com.logicacmg.koa.controller.beans.ControllerBean)container.preInvoke(this, 18, _EJS_s);
			beanRef.unsubscribe(sComponentID);
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
			container.postInvoke(this, 18, _EJS_s);
		}
		return ;
	}
}
