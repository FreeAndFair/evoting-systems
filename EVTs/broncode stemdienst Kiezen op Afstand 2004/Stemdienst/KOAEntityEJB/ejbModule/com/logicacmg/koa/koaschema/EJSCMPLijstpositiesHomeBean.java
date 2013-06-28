package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import com.ibm.ejs.persistence.*;
import com.ibm.ejs.EJSException;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSCMPLijstpositiesHomeBean
 * @generated
 */
public class EJSCMPLijstpositiesHomeBean extends EJSHome {
	/**
	 * EJSCMPLijstpositiesHomeBean
	 * @generated
	 */
	public EJSCMPLijstpositiesHomeBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Lijstposities create(java.lang.String positienummer, com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Lijstposities _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.LijstpositiesBean bean = (com.logicacmg.koa.koaschema.LijstpositiesBean) beanO.getEnterpriseBean();
			bean.ejbCreate(positienummer, argFk_klkr_1);
			_EJS_result = (com.logicacmg.koa.koaschema.Lijstposities) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(positienummer, argFk_klkr_1);
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
	public com.logicacmg.koa.koaschema.Lijstposities findByPrimaryKey(com.logicacmg.koa.koaschema.LijstpositiesKey primaryKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		return ((com.logicacmg.koa.koaschema.EJSJDBCPersisterCMPLijstpositiesBean) persister).findByPrimaryKey(primaryKey);
	}
	/**
	 * findLijstpositiesByFk_klkr_1
	 * @generated
	 */
	public java.util.Enumeration findLijstpositiesByFk_klkr_1(com.logicacmg.koa.koaschema.KieslijstenKey inKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
return super.getEnumeration(((com.logicacmg.koa.koaschema.EJSFinderLijstpositiesBean)persister).findLijstpositiesByFk_klkr_1(inKey));	}
	/**
	 * create
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Lijstposities create(java.lang.String positienummer, com.logicacmg.koa.koaschema.Kieslijsten argFk_klkr_1, java.lang.String achternaam, java.lang.String voorletters, java.lang.String roepnaam, char geslacht, java.lang.String woonplaats) throws javax.ejb.CreateException, java.rmi.RemoteException {
		BeanO beanO = null;
		com.logicacmg.koa.koaschema.Lijstposities _EJS_result = null;
		boolean createFailed = false;
		try {
			beanO = super.createBeanO();
			com.logicacmg.koa.koaschema.LijstpositiesBean bean = (com.logicacmg.koa.koaschema.LijstpositiesBean) beanO.getEnterpriseBean();
			bean.ejbCreate(positienummer, argFk_klkr_1, achternaam, voorletters, roepnaam, geslacht, woonplaats);
			_EJS_result = (com.logicacmg.koa.koaschema.Lijstposities) super.postCreate(beanO, keyFromBean(bean));
			bean.ejbPostCreate(positienummer, argFk_klkr_1, achternaam, voorletters, roepnaam, geslacht, woonplaats);
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
		com.logicacmg.koa.koaschema.LijstpositiesBean tmpEJB = (com.logicacmg.koa.koaschema.LijstpositiesBean) generalEJB;
		com.logicacmg.koa.koaschema.LijstpositiesKey keyClass = new com.logicacmg.koa.koaschema.LijstpositiesKey();
		keyClass.positienummer = tmpEJB.positienummer;
		keyClass.fk_klkr_1_kieslijstnummer = tmpEJB.fk_klkr_1_kieslijstnummer;
		keyClass.fk_klkr_1_fk_kkr_1_kieskringnummer = tmpEJB.fk_klkr_1_fk_kkr_1_kieskringnummer;
		return keyClass;
	}
	/**
	 * keyFromFields
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.LijstpositiesKey keyFromFields(java.lang.String f0, java.lang.String f1, java.lang.String f2) {
		com.logicacmg.koa.koaschema.LijstpositiesKey keyClass = new com.logicacmg.koa.koaschema.LijstpositiesKey();
		keyClass.positienummer = f0;
		keyClass.fk_klkr_1_kieslijstnummer = f1;
		keyClass.fk_klkr_1_fk_kkr_1_kieskringnummer = f2;
		return keyClass;
	}
}
