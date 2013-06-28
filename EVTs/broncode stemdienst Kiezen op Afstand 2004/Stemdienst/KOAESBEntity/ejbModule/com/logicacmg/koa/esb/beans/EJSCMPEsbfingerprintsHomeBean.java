package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPEsbfingerprintsHomeBean
 * @generated
 */
public class EJSCMPEsbfingerprintsHomeBean extends EJSHome {
	/**
	 * EJSCMPEsbfingerprintsHomeBean
	 * @generated
	 */
	public EJSCMPEsbfingerprintsHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints findByPrimaryKey(com.logicacmg.koa.esb.beans.EsbfingerprintsKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.esb.beans.EJSJDBCPersisterCMPEsbfingerprintsBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints create(java.math.BigDecimal id) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.esb.beans.Esbfingerprints _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.esb.beans.EsbfingerprintsBean bean = (com.logicacmg.koa.esb.beans.EsbfingerprintsBean) beanO.getEnterpriseBean();
			bean.ejbCreate(id);
			_EJS_result = (com.logicacmg.koa.esb.beans.Esbfingerprints) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(id);
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
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints findLatestFingerprint() throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.esb.beans.EJSJDBCPersisterCMPEsbfingerprintsBean)persister).findLatestFingerprint();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints create(java.math.BigDecimal id, byte[] xFingerprint, java.sql.Timestamp xTimestamp, java.lang.String sSystemState) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.esb.beans.Esbfingerprints _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.esb.beans.EsbfingerprintsBean bean = (com.logicacmg.koa.esb.beans.EsbfingerprintsBean) beanO.getEnterpriseBean();
			bean.ejbCreate(id, xFingerprint, xTimestamp, sSystemState);
			_EJS_result = (com.logicacmg.koa.esb.beans.Esbfingerprints) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(id, xFingerprint, xTimestamp, sSystemState);
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
		com.logicacmg.koa.esb.beans.EsbfingerprintsBean tmpEJB = (com.logicacmg.koa.esb.beans.EsbfingerprintsBean) generalEJB;
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey keyClass = new com.logicacmg.koa.esb.beans.EsbfingerprintsKey();
		keyClass.id = tmpEJB.id;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.EsbfingerprintsKey keyFromFields(java.math.BigDecimal f0) {
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey keyClass = new com.logicacmg.koa.esb.beans.EsbfingerprintsKey();
		keyClass.id = f0;
		return keyClass;
	}
}
