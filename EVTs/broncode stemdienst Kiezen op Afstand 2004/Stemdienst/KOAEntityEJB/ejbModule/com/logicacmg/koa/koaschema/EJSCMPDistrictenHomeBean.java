package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPDistrictenHomeBean
 * @generated
 */
public class EJSCMPDistrictenHomeBean extends EJSHome {
	/**
	 * EJSCMPDistrictenHomeBean
	 * @generated
	 */
	public EJSCMPDistrictenHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findDistrictenByFk_dist_kkr
	 * @generated
	 */
	public java.util.Enumeration findDistrictenByFk_dist_kkr(com.logicacmg.koa.koaschema.KieskringenKey inKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
return super.getEnumeration(((com.logicacmg.koa.koaschema.EJSFinderDistrictenBean)persister).findDistrictenByFk_dist_kkr(inKey));	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Districten findByPrimaryKey(com.logicacmg.koa.koaschema.DistrictenKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.koaschema.EJSJDBCPersisterCMPDistrictenBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Districten create(java.lang.String districtnummer) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Districten _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.DistrictenBean bean = (com.logicacmg.koa.koaschema.DistrictenBean) beanO.getEnterpriseBean();
			bean.ejbCreate(districtnummer);
			_EJS_result = (com.logicacmg.koa.koaschema.Districten) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(districtnummer);
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
		com.logicacmg.koa.koaschema.DistrictenBean tmpEJB = (com.logicacmg.koa.koaschema.DistrictenBean) generalEJB;
		com.logicacmg.koa.koaschema.DistrictenKey keyClass = new com.logicacmg.koa.koaschema.DistrictenKey();
		keyClass.districtnummer = tmpEJB.districtnummer;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.DistrictenKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.koaschema.DistrictenKey keyClass = new com.logicacmg.koa.koaschema.DistrictenKey();
		keyClass.districtnummer = f0;
		return keyClass;
	}
}
