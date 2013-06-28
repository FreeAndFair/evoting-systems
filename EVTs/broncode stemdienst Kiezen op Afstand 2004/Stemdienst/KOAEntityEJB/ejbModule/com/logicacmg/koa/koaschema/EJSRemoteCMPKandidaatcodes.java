package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPKandidaatcodes
 * @generated
 */
public class EJSRemoteCMPKandidaatcodes extends EJSWrapper implements Kandidaatcodes {
	/**
	 * EJSRemoteCMPKandidaatcodes
	 * @generated
	 */
	public EJSRemoteCMPKandidaatcodes() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getFk_kkrklpn_1
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Lijstposities getFk_kkrklpn_1() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.Lijstposities _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.KandidaatcodesBean beanRef = (com.logicacmg.koa.koaschema.KandidaatcodesBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getFk_kkrklpn_1();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
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
	 * getFk_kkrklpn_1Key
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.LijstpositiesKey getFk_kkrklpn_1Key() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.LijstpositiesKey _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.KandidaatcodesBean beanRef = (com.logicacmg.koa.koaschema.KandidaatcodesBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getFk_kkrklpn_1Key();
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
	 * privateSetFk_kkrklpn_1Key
	 * @generated
	 */
	public void privateSetFk_kkrklpn_1Key(com.logicacmg.koa.koaschema.LijstpositiesKey inKey) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KandidaatcodesBean beanRef = (com.logicacmg.koa.koaschema.KandidaatcodesBean)container.preInvoke(this, 2, _EJS_s);
			beanRef.privateSetFk_kkrklpn_1Key(inKey);
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
	 * secondarySetFk_kkrklpn_1
	 * @generated
	 */
	public void secondarySetFk_kkrklpn_1(com.logicacmg.koa.koaschema.Lijstposities aFk_kkrklpn_1) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KandidaatcodesBean beanRef = (com.logicacmg.koa.koaschema.KandidaatcodesBean)container.preInvoke(this, 3, _EJS_s);
			beanRef.secondarySetFk_kkrklpn_1(aFk_kkrklpn_1);
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
	 * setFk_kkrklpn_1
	 * @generated
	 */
	public void setFk_kkrklpn_1(com.logicacmg.koa.koaschema.Lijstposities aFk_kkrklpn_1) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KandidaatcodesBean beanRef = (com.logicacmg.koa.koaschema.KandidaatcodesBean)container.preInvoke(this, 4, _EJS_s);
			beanRef.setFk_kkrklpn_1(aFk_kkrklpn_1);
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
}
