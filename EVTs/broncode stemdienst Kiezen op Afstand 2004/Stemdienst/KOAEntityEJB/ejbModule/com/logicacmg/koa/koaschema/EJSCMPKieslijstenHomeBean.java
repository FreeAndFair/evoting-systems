package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKieslijstenHomeBean
 * @generated
 */
public class EJSCMPKieslijstenHomeBean extends EJSHome {
	/**
	 * EJSCMPKieslijstenHomeBean
	 * @generated
	 */
	public EJSCMPKieslijstenHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findKieslijstenByFk_kkr_1
	 * @generated
	 */
	public java.util.Enumeration findKieslijstenByFk_kkr_1(com.logicacmg.koa.koaschema.KieskringenKey inKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
return super.getEnumeration(((com.logicacmg.koa.koaschema.EJSFinderKieslijstenBean)persister).findKieslijstenByFk_kkr_1(inKey));	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieslijsten create(java.lang.String kieslijstnummer, com.logicacmg.koa.koaschema.Kieskringen argFk_kkr_1) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Kieslijsten _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.KieslijstenBean bean = (com.logicacmg.koa.koaschema.KieslijstenBean) beanO.getEnterpriseBean();
			bean.ejbCreate(kieslijstnummer, argFk_kkr_1);
			_EJS_result = (com.logicacmg.koa.koaschema.Kieslijsten) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(kieslijstnummer, argFk_kkr_1);
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
	public com.logicacmg.koa.koaschema.Kieslijsten create(java.lang.String kieslijstnummer, com.logicacmg.koa.koaschema.Kieskringen argFk_kkr_1, java.lang.String lijstnaam) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Kieslijsten _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.KieslijstenBean bean = (com.logicacmg.koa.koaschema.KieslijstenBean) beanO.getEnterpriseBean();
			bean.ejbCreate(kieslijstnummer, argFk_kkr_1, lijstnaam);
			_EJS_result = (com.logicacmg.koa.koaschema.Kieslijsten) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(kieslijstnummer, argFk_kkr_1, lijstnaam);
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
	public com.logicacmg.koa.koaschema.Kieslijsten findByPrimaryKey(com.logicacmg.koa.koaschema.KieslijstenKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.koaschema.EJSJDBCPersisterCMPKieslijstenBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.koaschema.KieslijstenBean tmpEJB = (com.logicacmg.koa.koaschema.KieslijstenBean) generalEJB;
		com.logicacmg.koa.koaschema.KieslijstenKey keyClass = new com.logicacmg.koa.koaschema.KieslijstenKey();
		keyClass.kieslijstnummer = tmpEJB.kieslijstnummer;
		keyClass.fk_kkr_1_kieskringnummer = tmpEJB.fk_kkr_1_kieskringnummer;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.KieslijstenKey keyFromFields(java.lang.String f0, java.lang.String f1) {
		com.logicacmg.koa.koaschema.KieslijstenKey keyClass = new com.logicacmg.koa.koaschema.KieslijstenKey();
		keyClass.kieslijstnummer = f0;
		keyClass.fk_kkr_1_kieskringnummer = f1;
		return keyClass;
	}
}
