package com.logicacmg.koa.databeheer.ejb.session;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessKiesRegisterAdminHelper
 * @generated
 */
public class EJSRemoteStatelessKiesRegisterAdminHelper extends EJSWrapper implements KiesRegisterAdminHelper {
	/**
	 * EJSRemoteStatelessKiesRegisterAdminHelper
	 * @generated
	 */
	public EJSRemoteStatelessKiesRegisterAdminHelper() throws java.rmi.RemoteException {
		super();	}
	/**
	 * removeKiezer
	 * @generated
	 */
	public java.lang.String removeKiezer(java.lang.String sKiezerId) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean beanRef = (com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.removeKiezer(sKiezerId);
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
	 * insertKiezers
	 * @generated
	 */
	public java.lang.String[] insertKiezers(com.logicacmg.koa.databeheer.data.KiezerData[] kiezers, com.logicacmg.koa.kr.beans.KiezersHome xKiezersHome, com.logicacmg.koa.sar.SarHome xSarHome) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String[] _EJS_result = null;
		try {
			com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean beanRef = (com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.insertKiezers(kiezers, xKiezersHome, xSarHome);
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
	 * updateKiezers
	 * @generated
	 */
	public java.lang.String[] updateKiezers(com.logicacmg.koa.databeheer.data.KiezerData[] xKiezers, com.logicacmg.koa.kr.beans.KiezersHome xKiezersHome, com.logicacmg.koa.sar.SarHome xSarHome) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String[] _EJS_result = null;
		try {
			com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean beanRef = (com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.updateKiezers(xKiezers, xKiezersHome, xSarHome);
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
}
