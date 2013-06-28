package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKiezersHomeBean
 * @generated
 */
public class EJSCMPKiezersHomeBean extends EJSHome {
	/**
	 * EJSCMPKiezersHomeBean
	 * @generated
	 */
	public EJSCMPKiezersHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByPrimaryKey(com.logicacmg.koa.kr.beans.KiezersKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKiezersBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers create(java.lang.String sStemcode, java.lang.String sKiezersidentificatie, java.lang.String sHashedWachtwoord, java.lang.String sDistrictnummer, java.lang.String sKieskringnummer, java.lang.String sTransactienummer) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.kr.beans.Kiezers _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.kr.beans.KiezersBean bean = (com.logicacmg.koa.kr.beans.KiezersBean) beanO.getEnterpriseBean();
			bean.ejbCreate(sStemcode, sKiezersidentificatie, sHashedWachtwoord, sDistrictnummer, sKieskringnummer, sTransactienummer);
			_EJS_result = (com.logicacmg.koa.kr.beans.Kiezers) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(sStemcode, sKiezersidentificatie, sHashedWachtwoord, sDistrictnummer, sKieskringnummer, sTransactienummer);
		}
		catch (javax.ejb.CreateException ex) {
			createFailed = true;
			throw ex;
		} catch (java.rmi.RemoteException ex) {
			createFailed = true;
			throw ex;
		} catch (Throwable ex) {
			createFailed = true;
			throw new CreateFailureException(ex);
		} finally {
			if (createFailed) {
				super.createFailure(beanO);
			}
		}
		return _EJS_result;
	}
	/**
	 * findByKiezerId
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByKiezerId(java.lang.String sKiezerId) throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKiezersBean)persister).findByKiezerId(sKiezerId);	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers create() throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.kr.beans.Kiezers _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.kr.beans.KiezersBean bean = (com.logicacmg.koa.kr.beans.KiezersBean) beanO.getEnterpriseBean();
			bean.ejbCreate();
			_EJS_result = (com.logicacmg.koa.kr.beans.Kiezers) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate();
		}
		catch (javax.ejb.CreateException ex) {
			createFailed = true;
			throw ex;
		} catch (java.rmi.RemoteException ex) {
			createFailed = true;
			throw ex;
		} catch (Throwable ex) {
			createFailed = true;
			throw new CreateFailureException(ex);
		} finally {
			if (createFailed) {
				super.createFailure(beanO);
			}
		}
		return _EJS_result;
	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.kr.beans.KiezersBean tmpEJB = (com.logicacmg.koa.kr.beans.KiezersBean) generalEJB;
		com.logicacmg.koa.kr.beans.KiezersKey keyClass = new com.logicacmg.koa.kr.beans.KiezersKey();
		keyClass.stemcode = tmpEJB.stemcode;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KiezersKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.kr.beans.KiezersKey keyClass = new com.logicacmg.koa.kr.beans.KiezersKey();
		keyClass.stemcode = f0;
		return keyClass;
	}
}
