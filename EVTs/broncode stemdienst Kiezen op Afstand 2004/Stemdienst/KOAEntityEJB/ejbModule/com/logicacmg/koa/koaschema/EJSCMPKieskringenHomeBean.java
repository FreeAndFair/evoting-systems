package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKieskringenHomeBean
 * @generated
 */
public class EJSCMPKieskringenHomeBean extends EJSHome {
	/**
	 * EJSCMPKieskringenHomeBean
	 * @generated
	 */
	public EJSCMPKieskringenHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieskringen findByPrimaryKey(com.logicacmg.koa.koaschema.KieskringenKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.koaschema.EJSJDBCPersisterCMPKieskringenBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieskringen create(java.lang.String kieskringnummer) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Kieskringen _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.KieskringenBean bean = (com.logicacmg.koa.koaschema.KieskringenBean) beanO.getEnterpriseBean();
			bean.ejbCreate(kieskringnummer);
			_EJS_result = (com.logicacmg.koa.koaschema.Kieskringen) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(kieskringnummer);
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
		com.logicacmg.koa.koaschema.KieskringenBean tmpEJB = (com.logicacmg.koa.koaschema.KieskringenBean) generalEJB;
		com.logicacmg.koa.koaschema.KieskringenKey keyClass = new com.logicacmg.koa.koaschema.KieskringenKey();
		keyClass.kieskringnummer = tmpEJB.kieskringnummer;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.koaschema.KieskringenKey keyClass = new com.logicacmg.koa.koaschema.KieskringenKey();
		keyClass.kieskringnummer = f0;
		return keyClass;
	}
}
