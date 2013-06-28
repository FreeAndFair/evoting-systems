package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPEncryptedesbHomeBean
 * @generated
 */
public class EJSCMPEncryptedesbHomeBean extends EJSHome {
	/**
	 * EJSCMPEncryptedesbHomeBean
	 * @generated
	 */
	public EJSCMPEncryptedesbHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Encryptedesb create(java.math.BigDecimal stemnummer) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.esb.beans.Encryptedesb _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.esb.beans.EncryptedesbBean bean = (com.logicacmg.koa.esb.beans.EncryptedesbBean) beanO.getEnterpriseBean();
			bean.ejbCreate(stemnummer);
			_EJS_result = (com.logicacmg.koa.esb.beans.Encryptedesb) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(stemnummer);
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
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Encryptedesb create(java.math.BigDecimal stemnummer, byte[] encryptedvote) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.esb.beans.Encryptedesb _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.esb.beans.EncryptedesbBean bean = (com.logicacmg.koa.esb.beans.EncryptedesbBean) beanO.getEnterpriseBean();
			bean.ejbCreate(stemnummer, encryptedvote);
			_EJS_result = (com.logicacmg.koa.esb.beans.Encryptedesb) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(stemnummer, encryptedvote);
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
	public com.logicacmg.koa.esb.beans.Encryptedesb findByPrimaryKey(com.logicacmg.koa.esb.beans.EncryptedesbKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.esb.beans.EJSJDBCPersisterCMPEncryptedesbBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.esb.beans.EncryptedesbBean tmpEJB = (com.logicacmg.koa.esb.beans.EncryptedesbBean) generalEJB;
		com.logicacmg.koa.esb.beans.EncryptedesbKey keyClass = new com.logicacmg.koa.esb.beans.EncryptedesbKey();
		keyClass.stemnummer = tmpEJB.stemnummer;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.EncryptedesbKey keyFromFields(java.math.BigDecimal f0) {
		com.logicacmg.koa.esb.beans.EncryptedesbKey keyClass = new com.logicacmg.koa.esb.beans.EncryptedesbKey();
		keyClass.stemnummer = f0;
		return keyClass;
	}
}
