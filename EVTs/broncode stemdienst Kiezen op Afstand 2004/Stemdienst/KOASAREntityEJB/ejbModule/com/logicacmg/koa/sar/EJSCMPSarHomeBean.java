package com.logicacmg.koa.sar;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPSarHomeBean
 * @generated
 */
public class EJSCMPSarHomeBean extends EJSHome {
	/**
	 * EJSCMPSarHomeBean
	 * @generated
	 */
	public EJSCMPSarHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.sar.Sar findByPrimaryKey(com.logicacmg.koa.sar.SarKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.sar.EJSJDBCPersisterCMPSarBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * findByStemcode
	 * @generated
	 */
	public com.logicacmg.koa.sar.Sar findByStemcode(java.lang.String sStemcode) throws javax.ejb.FinderException, java.rmi.RemoteException {
return ((com.logicacmg.koa.sar.EJSJDBCPersisterCMPSarBean)persister).findByStemcode(sStemcode);	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.sar.Sar create(java.lang.String kiezeridentificatie, java.lang.String stemcode) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.sar.Sar _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.sar.SarBean bean = (com.logicacmg.koa.sar.SarBean) beanO.getEnterpriseBean();
			bean.ejbCreate(kiezeridentificatie, stemcode);
			_EJS_result = (com.logicacmg.koa.sar.Sar) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(kiezeridentificatie, stemcode);
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
		com.logicacmg.koa.sar.SarBean tmpEJB = (com.logicacmg.koa.sar.SarBean) generalEJB;
		com.logicacmg.koa.sar.SarKey keyClass = new com.logicacmg.koa.sar.SarKey();
		keyClass.kiezeridentificatie = tmpEJB.kiezeridentificatie;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.sar.SarKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.sar.SarKey keyClass = new com.logicacmg.koa.sar.SarKey();
		keyClass.kiezeridentificatie = f0;
		return keyClass;
	}
}
