package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKRFingerprintsHomeBean
 * @generated
 */
public class EJSCMPKRFingerprintsHomeBean extends EJSHome {
	/**
	 * EJSCMPKRFingerprintsHomeBean
	 * @generated
	 */
	public EJSCMPKRFingerprintsHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLatestFingerprint(java.lang.Integer type) throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKRFingerprintsBean)persister).findLatestFingerprint(type);	}
	/**
	 * findLastDynamicFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastDynamicFP(java.lang.Integer type, java.lang.String firstState, java.lang.String secondState) throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKRFingerprintsBean)persister).findLastDynamicFP(type, firstState, secondState);	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByPrimaryKey(com.logicacmg.koa.kr.beans.KRFingerprintsKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKRFingerprintsBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints create() throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.kr.beans.KRFingerprintsBean bean = (com.logicacmg.koa.kr.beans.KRFingerprintsBean) beanO.getEnterpriseBean();
			bean.ejbCreate();
			_EJS_result = (com.logicacmg.koa.kr.beans.KRFingerprints) super.postCreate(beanO, keyFromBean(bean));
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
	 * findByTypeAndState
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByTypeAndState(java.lang.Integer type, java.lang.String systemstatus) throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKRFingerprintsBean)persister).findByTypeAndState(type, systemstatus);	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints create(java.math.BigDecimal xId, java.lang.Short xType, byte[] xFingerprint, java.sql.Timestamp xTimestamp, java.lang.String sSystemState) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.kr.beans.KRFingerprints _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.kr.beans.KRFingerprintsBean bean = (com.logicacmg.koa.kr.beans.KRFingerprintsBean) beanO.getEnterpriseBean();
			bean.ejbCreate(xId, xType, xFingerprint, xTimestamp, sSystemState);
			_EJS_result = (com.logicacmg.koa.kr.beans.KRFingerprints) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(xId, xType, xFingerprint, xTimestamp, sSystemState);
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
	 * findLastFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastFP() throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKRFingerprintsBean)persister).findLastFP();	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.kr.beans.KRFingerprintsBean tmpEJB = (com.logicacmg.koa.kr.beans.KRFingerprintsBean) generalEJB;
		com.logicacmg.koa.kr.beans.KRFingerprintsKey keyClass = new com.logicacmg.koa.kr.beans.KRFingerprintsKey();
		keyClass.id = tmpEJB.id;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprintsKey keyFromFields(java.math.BigDecimal f0) {
		com.logicacmg.koa.kr.beans.KRFingerprintsKey keyClass = new com.logicacmg.koa.kr.beans.KRFingerprintsKey();
		keyClass.id = f0;
		return keyClass;
	}
}
