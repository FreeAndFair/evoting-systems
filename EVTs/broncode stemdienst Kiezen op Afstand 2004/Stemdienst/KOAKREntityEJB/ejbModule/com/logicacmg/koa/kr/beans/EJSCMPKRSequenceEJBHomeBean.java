package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKRSequenceEJBHomeBean
 * @generated
 */
public class EJSCMPKRSequenceEJBHomeBean extends EJSHome {
	/**
	 * EJSCMPKRSequenceEJBHomeBean
	 * @generated
	 */
	public EJSCMPKRSequenceEJBHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRSequenceEJB findByPrimaryKey(com.logicacmg.koa.kr.beans.KRSequenceEJBKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPKRSequenceEJBBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRSequenceEJB create() throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.kr.beans.KRSequenceEJB _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.kr.beans.KRSequenceEJBBean bean = (com.logicacmg.koa.kr.beans.KRSequenceEJBBean) beanO.getEnterpriseBean();
			bean.ejbCreate();
			_EJS_result = (com.logicacmg.koa.kr.beans.KRSequenceEJB) super.postCreate(beanO, keyFromBean(bean));
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
		com.logicacmg.koa.kr.beans.KRSequenceEJBBean tmpEJB = (com.logicacmg.koa.kr.beans.KRSequenceEJBBean) generalEJB;
		com.logicacmg.koa.kr.beans.KRSequenceEJBKey keyClass = new com.logicacmg.koa.kr.beans.KRSequenceEJBKey();
		keyClass.tablename = tmpEJB.tablename;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRSequenceEJBKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.kr.beans.KRSequenceEJBKey keyClass = new com.logicacmg.koa.kr.beans.KRSequenceEJBKey();
		keyClass.tablename = f0;
		return keyClass;
	}
}
