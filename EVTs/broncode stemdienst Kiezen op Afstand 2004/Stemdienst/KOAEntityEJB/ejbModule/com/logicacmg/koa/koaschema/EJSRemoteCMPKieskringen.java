package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPKieskringen
 * @generated
 */
public class EJSRemoteCMPKieskringen extends EJSWrapper implements Kieskringen {
	/**
	 * EJSRemoteCMPKieskringen
	 * @generated
	 */
	public EJSRemoteCMPKieskringen() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getKieskringnaam
	 * @generated
	 */
	public java.lang.String getKieskringnaam() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getKieskringnaam();
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
	 * getDistricten
	 * @generated
	 */
	public java.util.Enumeration getDistricten() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Enumeration _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getDistricten();
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
			container.postInvoke(this, 1, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getKieslijsten
	 * @generated
	 */
	public java.util.Enumeration getKieslijsten() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Enumeration _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.getKieslijsten();
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
			container.postInvoke(this, 2, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * addDistricten
	 * @generated
	 */
	public void addDistricten(com.logicacmg.koa.koaschema.Districten aDistricten) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 3, _EJS_s);
			beanRef.addDistricten(aDistricten);
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
	 * removeDistricten
	 * @generated
	 */
	public void removeDistricten(com.logicacmg.koa.koaschema.Districten aDistricten) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 4, _EJS_s);
			beanRef.removeDistricten(aDistricten);
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
	 * secondaryAddDistricten
	 * @generated
	 */
	public void secondaryAddDistricten(com.logicacmg.koa.koaschema.Districten aDistricten) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 5, _EJS_s);
			beanRef.secondaryAddDistricten(aDistricten);
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
	 * secondaryAddKieslijsten
	 * @generated
	 */
	public void secondaryAddKieslijsten(com.logicacmg.koa.koaschema.Kieslijsten aKieslijsten) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 6, _EJS_s);
			beanRef.secondaryAddKieslijsten(aKieslijsten);
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
	/**
	 * secondaryRemoveDistricten
	 * @generated
	 */
	public void secondaryRemoveDistricten(com.logicacmg.koa.koaschema.Districten aDistricten) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 7, _EJS_s);
			beanRef.secondaryRemoveDistricten(aDistricten);
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
		return ;
	}
	/**
	 * secondaryRemoveKieslijsten
	 * @generated
	 */
	public void secondaryRemoveKieslijsten(com.logicacmg.koa.koaschema.Kieslijsten aKieslijsten) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 8, _EJS_s);
			beanRef.secondaryRemoveKieslijsten(aKieslijsten);
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
		return ;
	}
	/**
	 * setKieskringnaam
	 * @generated
	 */
	public void setKieskringnaam(java.lang.String newKieskringnaam) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.KieskringenBean beanRef = (com.logicacmg.koa.koaschema.KieskringenBean)container.preInvoke(this, 9, _EJS_s);
			beanRef.setKieskringnaam(newKieskringnaam);
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
		return ;
	}
}
