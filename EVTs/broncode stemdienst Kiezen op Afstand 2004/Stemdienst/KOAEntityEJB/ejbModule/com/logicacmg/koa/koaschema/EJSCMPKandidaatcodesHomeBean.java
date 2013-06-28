package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPKandidaatcodesHomeBean
 * @generated
 */
public class EJSCMPKandidaatcodesHomeBean extends EJSHome {
	/**
	 * EJSCMPKandidaatcodesHomeBean
	 * @generated
	 */
	public EJSCMPKandidaatcodesHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kandidaatcodes findByPrimaryKey(com.logicacmg.koa.koaschema.KandidaatcodesKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.koaschema.EJSJDBCPersisterCMPKandidaatcodesBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kandidaatcodes create(java.lang.String kandidaatcode, java.lang.String positienummer, java.lang.String kieslijstnummer, java.lang.String kieskringnummer) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Kandidaatcodes _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.KandidaatcodesBean bean = (com.logicacmg.koa.koaschema.KandidaatcodesBean) beanO.getEnterpriseBean();
			bean.ejbCreate(kandidaatcode, positienummer, kieslijstnummer, kieskringnummer);
			_EJS_result = (com.logicacmg.koa.koaschema.Kandidaatcodes) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(kandidaatcode, positienummer, kieslijstnummer, kieskringnummer);
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
	public com.logicacmg.koa.koaschema.Kandidaatcodes create(java.lang.String kandidaatcode) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Kandidaatcodes _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.KandidaatcodesBean bean = (com.logicacmg.koa.koaschema.KandidaatcodesBean) beanO.getEnterpriseBean();
			bean.ejbCreate(kandidaatcode);
			_EJS_result = (com.logicacmg.koa.koaschema.Kandidaatcodes) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(kandidaatcode);
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
	 * findKandidaatcodesByFk_kkrklpn_1
	 * @generated
	 */
	public java.util.Enumeration findKandidaatcodesByFk_kkrklpn_1(com.logicacmg.koa.koaschema.LijstpositiesKey inKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
return super.getEnumeration(((com.logicacmg.koa.koaschema.EJSFinderKandidaatcodesBean)persister).findKandidaatcodesByFk_kkrklpn_1(inKey));	}
	/**
	 * keyFromBean
	 * @generated
	 */
	public Object keyFromBean(javax.ejb.EntityBean generalEJB) {
		com.logicacmg.koa.koaschema.KandidaatcodesBean tmpEJB = (com.logicacmg.koa.koaschema.KandidaatcodesBean) generalEJB;
		com.logicacmg.koa.koaschema.KandidaatcodesKey keyClass = new com.logicacmg.koa.koaschema.KandidaatcodesKey();
		keyClass.kandidaatcode = tmpEJB.kandidaatcode;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.KandidaatcodesKey keyFromFields(java.lang.String f0) {
		com.logicacmg.koa.koaschema.KandidaatcodesKey keyClass = new com.logicacmg.koa.koaschema.KandidaatcodesKey();
		keyClass.kandidaatcode = f0;
		return keyClass;
	}
}
