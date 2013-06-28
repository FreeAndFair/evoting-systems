package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPTransactioncodeHomeBean
 * @generated
 */
public class EJSCMPTransactioncodeHomeBean extends EJSHome {
	/**
	 * EJSCMPTransactioncodeHomeBean
	 * @generated
	 */
	public EJSCMPTransactioncodeHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Transactioncode findByPrimaryKey(com.logicacmg.koa.kr.beans.TransactioncodeKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.kr.beans.EJSJDBCPersisterCMPTransactioncodeBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Transactioncode create(java.lang.String transactienummer) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.kr.beans.Transactioncode _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.kr.beans.TransactioncodeBean bean = (com.logicacmg.koa.kr.beans.TransactioncodeBean) beanO.getEnterpriseBean();
			bean.ejbCreate(transactienummer);
			_EJS_result = (com.logicacmg.koa.kr.beans.Transactioncode) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(transactienummer);
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
		com.logicacmg.koa.kr.beans.TransactioncodeBean tmpEJB = (com.logicacmg.koa.kr.beans.TransactioncodeBean) generalEJB;
		com.logicacmg.koa.kr.beans.TransactioncodeKey keyClass = new com.logicacmg.koa.kr.beans.TransactioncodeKey();
		keyClass.transactienummer = tmpEJB.transactienummer;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.TransactioncodeKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.kr.beans.TransactioncodeKey keyClass = new com.logicacmg.koa.kr.beans.TransactioncodeKey();
		keyClass.transactienummer = f0;
		return keyClass;
	}
}
