package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPESBSequencesEJBHomeBean
 * @generated
 */
public class EJSCMPESBSequencesEJBHomeBean extends EJSHome {
	/**
	 * EJSCMPESBSequencesEJBHomeBean
	 * @generated
	 */
	public EJSCMPESBSequencesEJBHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.ESBSequencesEJB findByPrimaryKey(com.logicacmg.koa.esb.beans.ESBSequencesEJBKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.esb.beans.EJSJDBCPersisterCMPESBSequencesEJBBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.ESBSequencesEJB create() throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.esb.beans.ESBSequencesEJB _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.esb.beans.ESBSequencesEJBBean bean = (com.logicacmg.koa.esb.beans.ESBSequencesEJBBean) beanO.getEnterpriseBean();
			bean.ejbCreate();
			_EJS_result = (com.logicacmg.koa.esb.beans.ESBSequencesEJB) super.postCreate(beanO, keyFromBean(bean));
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
		com.logicacmg.koa.esb.beans.ESBSequencesEJBBean tmpEJB = (com.logicacmg.koa.esb.beans.ESBSequencesEJBBean) generalEJB;
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey keyClass = new com.logicacmg.koa.esb.beans.ESBSequencesEJBKey();
		keyClass.tablename = tmpEJB.tablename;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.ESBSequencesEJBKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey keyClass = new com.logicacmg.koa.esb.beans.ESBSequencesEJBKey();
		keyClass.tablename = f0;
		return keyClass;
	}
}
