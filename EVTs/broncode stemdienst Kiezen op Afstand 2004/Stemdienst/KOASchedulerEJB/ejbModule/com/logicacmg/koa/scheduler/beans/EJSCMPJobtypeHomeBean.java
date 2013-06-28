package com.logicacmg.koa.scheduler.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPJobtypeHomeBean
 * @generated
 */
public class EJSCMPJobtypeHomeBean extends EJSHome {
	/**
	 * EJSCMPJobtypeHomeBean
	 * @generated
	 */
	public EJSCMPJobtypeHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype create(java.math.BigDecimal typeid) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.scheduler.beans.Jobtype _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.scheduler.beans.JobtypeBean bean = (com.logicacmg.koa.scheduler.beans.JobtypeBean) beanO.getEnterpriseBean();
			bean.ejbCreate(typeid);
			_EJS_result = (com.logicacmg.koa.scheduler.beans.Jobtype) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(typeid);
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
	public com.logicacmg.koa.scheduler.beans.Jobtype findByPrimaryKey(com.logicacmg.koa.scheduler.beans.JobtypeKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.scheduler.beans.EJSJDBCPersisterCMPJobtypeBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.scheduler.beans.JobtypeBean tmpEJB = (com.logicacmg.koa.scheduler.beans.JobtypeBean) generalEJB;
		com.logicacmg.koa.scheduler.beans.JobtypeKey keyClass = new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		keyClass.typeid = tmpEJB.typeid;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.scheduler.beans.JobtypeKey keyFromFields(java.math.BigDecimal f0) {
		com.logicacmg.koa.scheduler.beans.JobtypeKey keyClass = new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		keyClass.typeid = f0;
		return keyClass;
	}
}
