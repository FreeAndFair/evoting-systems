package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPKiezers
 * @generated
 */
public class EJSRemoteCMPKiezers extends EJSWrapper implements Kiezers {
	/**
	 * EJSRemoteCMPKiezers
	 * @generated
	 */
	public EJSRemoteCMPKiezers() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getAccountlocked
	 * @generated
	 */
	public java.lang.Boolean getAccountlocked() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Boolean _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getAccountlocked();
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
	 * getReedsgestemd
	 * @generated
	 */
	public java.lang.Boolean getReedsgestemd() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Boolean _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getReedsgestemd();
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
	 * getVerwijderd
	 * @generated
	 */
	public java.lang.Boolean getVerwijderd() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Boolean _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.getVerwijderd();
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
	 * getInvalidlogins
	 * @generated
	 */
	public java.lang.Integer getInvalidlogins() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Integer _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.getInvalidlogins();
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
	 * getLoginattemptsleft
	 * @generated
	 */
	public java.lang.Integer getLoginattemptsleft() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Integer _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = beanRef.getLoginattemptsleft();
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
	 * getValidlogins
	 * @generated
	 */
	public java.lang.Integer getValidlogins() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Integer _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 5, _EJS_s);
			_EJS_result = beanRef.getValidlogins();
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
	 * getDistrictnummer
	 * @generated
	 */
	public java.lang.String getDistrictnummer() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 6, _EJS_s);
			_EJS_result = beanRef.getDistrictnummer();
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
	 * getHashedwachtwoord
	 * @generated
	 */
	public java.lang.String getHashedwachtwoord() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 7, _EJS_s);
			_EJS_result = beanRef.getHashedwachtwoord();
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
	 * getKieskringnummer
	 * @generated
	 */
	public java.lang.String getKieskringnummer() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 8, _EJS_s);
			_EJS_result = beanRef.getKieskringnummer();
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
	 * getKiezeridentificatie
	 * @generated
	 */
	public java.lang.String getKiezeridentificatie() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 9, _EJS_s);
			_EJS_result = beanRef.getKiezeridentificatie();
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
	 * getModaliteit
	 * @generated
	 */
	public java.lang.String getModaliteit() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 10, _EJS_s);
			_EJS_result = beanRef.getModaliteit();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
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
	 * getStemcode
	 * @generated
	 */
	public java.lang.String getStemcode() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 11, _EJS_s);
			_EJS_result = beanRef.getStemcode();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
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
	 * getTransactienummer
	 * @generated
	 */
	public java.lang.String getTransactienummer() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 12, _EJS_s);
			_EJS_result = beanRef.getTransactienummer();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
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
	 * getTimelastsuccesfullogin
	 * @generated
	 */
	public java.sql.Timestamp getTimelastsuccesfullogin() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 13, _EJS_s);
			_EJS_result = beanRef.getTimelastsuccesfullogin();
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
	 * getTimestampGestemd
	 * @generated
	 */
	public java.sql.Timestamp getTimestampGestemd() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 14, _EJS_s);
			_EJS_result = beanRef.getTimestampGestemd();
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
	 * getTimestampunlock
	 * @generated
	 */
	public java.sql.Timestamp getTimestampunlock() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 15, _EJS_s);
			_EJS_result = beanRef.getTimestampunlock();
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
	 * setAccountlocked
	 * @generated
	 */
	public void setAccountlocked(java.lang.Boolean newAccountlocked) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 16, _EJS_s);
			beanRef.setAccountlocked(newAccountlocked);
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
	 * setDistrictnummer
	 * @generated
	 */
	public void setDistrictnummer(java.lang.String newDistrictnummer) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 17, _EJS_s);
			beanRef.setDistrictnummer(newDistrictnummer);
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
	 * setHashedwachtwoord
	 * @generated
	 */
	public void setHashedwachtwoord(java.lang.String newHashedwachtwoord) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 18, _EJS_s);
			beanRef.setHashedwachtwoord(newHashedwachtwoord);
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
	/**
	 * setInvalidlogins
	 * @generated
	 */
	public void setInvalidlogins(java.lang.Integer newInvalidlogins) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 19, _EJS_s);
			beanRef.setInvalidlogins(newInvalidlogins);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 19, _EJS_s);
		}
		return ;
	}
	/**
	 * setKieskringnummer
	 * @generated
	 */
	public void setKieskringnummer(java.lang.String newKieskringnummer) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 20, _EJS_s);
			beanRef.setKieskringnummer(newKieskringnummer);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 20, _EJS_s);
		}
		return ;
	}
	/**
	 * setKiezeridentificatie
	 * @generated
	 */
	public void setKiezeridentificatie(java.lang.String newKiezeridentificatie) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 21, _EJS_s);
			beanRef.setKiezeridentificatie(newKiezeridentificatie);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 21, _EJS_s);
		}
		return ;
	}
	/**
	 * setLoginattemptsleft
	 * @generated
	 */
	public void setLoginattemptsleft(java.lang.Integer newLoginattemptsleft) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 22, _EJS_s);
			beanRef.setLoginattemptsleft(newLoginattemptsleft);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 22, _EJS_s);
		}
		return ;
	}
	/**
	 * setModaliteit
	 * @generated
	 */
	public void setModaliteit(java.lang.String newModaliteit) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 23, _EJS_s);
			beanRef.setModaliteit(newModaliteit);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 23, _EJS_s);
		}
		return ;
	}
	/**
	 * setReedsgestemd
	 * @generated
	 */
	public void setReedsgestemd(java.lang.Boolean newReedsgestemd) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 24, _EJS_s);
			beanRef.setReedsgestemd(newReedsgestemd);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 24, _EJS_s);
		}
		return ;
	}
	/**
	 * setStemcode
	 * @generated
	 */
	public void setStemcode(java.lang.String newStemcode) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 25, _EJS_s);
			beanRef.setStemcode(newStemcode);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 25, _EJS_s);
		}
		return ;
	}
	/**
	 * setTimelastsuccesfullogin
	 * @generated
	 */
	public void setTimelastsuccesfullogin(java.sql.Timestamp newTimelastsuccesfullogin) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 26, _EJS_s);
			beanRef.setTimelastsuccesfullogin(newTimelastsuccesfullogin);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 26, _EJS_s);
		}
		return ;
	}
	/**
	 * setTimestampGestemd
	 * @generated
	 */
	public void setTimestampGestemd(java.sql.Timestamp newTimestampgestemd) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 27, _EJS_s);
			beanRef.setTimestampGestemd(newTimestampgestemd);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 27, _EJS_s);
		}
		return ;
	}
	/**
	 * setTimestampunlock
	 * @generated
	 */
	public void setTimestampunlock(java.sql.Timestamp newTimestampunlock) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 28, _EJS_s);
			beanRef.setTimestampunlock(newTimestampunlock);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 28, _EJS_s);
		}
		return ;
	}
	/**
	 * setTransactienummer
	 * @generated
	 */
	public void setTransactienummer(java.lang.String newTransactienummer) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 29, _EJS_s);
			beanRef.setTransactienummer(newTransactienummer);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 29, _EJS_s);
		}
		return ;
	}
	/**
	 * setValidlogins
	 * @generated
	 */
	public void setValidlogins(java.lang.Integer newValidlogins) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 30, _EJS_s);
			beanRef.setValidlogins(newValidlogins);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 30, _EJS_s);
		}
		return ;
	}
	/**
	 * setVerwijderd
	 * @generated
	 */
	public void setVerwijderd(java.lang.Boolean newVerwijderd) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kr.beans.KiezersBean beanRef = (com.logicacmg.koa.kr.beans.KiezersBean)container.preInvoke(this, 31, _EJS_s);
			beanRef.setVerwijderd(newVerwijderd);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 31, _EJS_s);
		}
		return ;
	}
}
