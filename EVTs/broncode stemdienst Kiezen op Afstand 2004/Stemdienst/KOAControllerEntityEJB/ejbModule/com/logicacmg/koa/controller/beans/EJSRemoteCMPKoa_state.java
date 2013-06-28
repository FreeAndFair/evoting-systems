package com.logicacmg.koa.controller.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPKoa_state
 * @generated
 */
public class EJSRemoteCMPKoa_state extends EJSWrapper implements Koa_state {
	/**
	 * EJSRemoteCMPKoa_state
	 * @generated
	 */
	public EJSRemoteCMPKoa_state() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getCurrent_state
	 * @generated
	 */
	public java.lang.String getCurrent_state() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.controller.beans.Koa_stateBean beanRef = (com.logicacmg.koa.controller.beans.Koa_stateBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getCurrent_state();
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
	 * setCurrent_state
	 * @generated
	 */
	public void setCurrent_state(java.lang.String newCurrent_state) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.controller.beans.Koa_stateBean beanRef = (com.logicacmg.koa.controller.beans.Koa_stateBean)container.preInvoke(this, 1, _EJS_s);
			beanRef.setCurrent_state(newCurrent_state);
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
		return ;
	}
}
