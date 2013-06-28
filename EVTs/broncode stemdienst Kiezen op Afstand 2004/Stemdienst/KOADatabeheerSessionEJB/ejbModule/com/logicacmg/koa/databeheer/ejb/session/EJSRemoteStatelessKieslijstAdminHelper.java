package com.logicacmg.koa.databeheer.ejb.session;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessKieslijstAdminHelper
 * @generated
 */
public class EJSRemoteStatelessKieslijstAdminHelper extends EJSWrapper implements KieslijstAdminHelper {
	/**
	 * EJSRemoteStatelessKieslijstAdminHelper
	 * @generated
	 */
	public EJSRemoteStatelessKieslijstAdminHelper() throws java.rmi.RemoteException {
		super();	}
	/**
	 * insertKieslijst
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieslijsten insertKieslijst(java.lang.String kiesKringNr, java.lang.String kieslijstNr, java.lang.String lijstnaam) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.Kieslijsten _EJS_result = null;
		try {
			com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelperBean beanRef = (com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelperBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.insertKieslijst(kiesKringNr, kieslijstNr, lijstnaam);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 0, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * insertLijstPostitie
	 * @generated
	 */
	public void insertLijstPostitie(com.logicacmg.koa.koaschema.Kieslijsten xKieslijst, java.lang.String sPositieNr, java.lang.String sAchternaam, java.lang.String sVoorletters, java.lang.String sRoepnaam, char sGeslacht, java.lang.String sWoonplaats) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelperBean beanRef = (com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelperBean)container.preInvoke(this, 1, _EJS_s);
			beanRef.insertLijstPostitie(xKieslijst, sPositieNr, sAchternaam, sVoorletters, sRoepnaam, sGeslacht, sWoonplaats);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 1, _EJS_s);
		}
		return ;
	}
}
