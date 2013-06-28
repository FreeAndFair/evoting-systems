package com.logicacmg.koa.controller.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKoa_stateHomeBean
 * @generated
 */
public class EJSCMPKoa_stateHomeBean extends EJSHome {
	/**
	 * EJSCMPKoa_stateHomeBean
	 * @generated
	 */
	public EJSCMPKoa_stateHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.controller.beans.Koa_state create(java.lang.Integer id) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.controller.beans.Koa_state _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.controller.beans.Koa_stateBean bean = (com.logicacmg.koa.controller.beans.Koa_stateBean) beanO.getEnterpriseBean();
			bean.ejbCreate(id);
			_EJS_result = (com.logicacmg.koa.controller.beans.Koa_state) super.postCreate(beanO, keyFromBean(bean));
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
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.controller.beans.Koa_state findByPrimaryKey(com.logicacmg.koa.controller.beans.Koa_stateKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.controller.beans.EJSJDBCPersisterCMPKoa_stateBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.controller.beans.Koa_stateBean tmpEJB = (com.logicacmg.koa.controller.beans.Koa_stateBean) generalEJB;
		com.logicacmg.koa.controller.beans.Koa_stateKey keyClass = new com.logicacmg.koa.controller.beans.Koa_stateKey();
		keyClass.id = tmpEJB.id;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.controller.beans.Koa_stateKey keyFromFields(java.lang.Integer f0) {
		com.logicacmg.koa.controller.beans.Koa_stateKey keyClass = new com.logicacmg.koa.controller.beans.Koa_stateKey();
		keyClass.id = f0;
		return keyClass;
	}
}
