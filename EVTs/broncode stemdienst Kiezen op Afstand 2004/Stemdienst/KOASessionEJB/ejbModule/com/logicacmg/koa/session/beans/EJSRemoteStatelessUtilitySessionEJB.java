package com.logicacmg.koa.session.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessUtilitySessionEJB
 * @generated
 */
public class EJSRemoteStatelessUtilitySessionEJB extends EJSWrapper implements UtilitySessionEJB {
	/**
	 * EJSRemoteStatelessUtilitySessionEJB
	 * @generated
	 */
	public EJSRemoteStatelessUtilitySessionEJB() throws java.rmi.RemoteException {
		super();	}
	/**
	 * logAuditRecord
	 * @generated
	 */
	public void logAuditRecord(int iSeverity, java.lang.String sAction, java.lang.String sComponent, java.lang.String sActor, java.lang.String sMessage) throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.session.beans.UtilitySessionEJBBean beanRef = (com.logicacmg.koa.session.beans.UtilitySessionEJBBean)container.preInvoke(this, 0, _EJS_s);
			beanRef.logAuditRecord(iSeverity, sAction, sComponent, sActor, sMessage);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 0, _EJS_s);
		}
		return ;
	}
	/**
	 * logTXAuditRecord
	 * @generated
	 */
	public void logTXAuditRecord(int iSeverity, java.lang.String sAction, java.lang.String sComponent, java.lang.String sActor, java.lang.String sMessage) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.session.beans.UtilitySessionEJBBean beanRef = (com.logicacmg.koa.session.beans.UtilitySessionEJBBean)container.preInvoke(this, 1, _EJS_s);
			beanRef.logTXAuditRecord(iSeverity, sAction, sComponent, sActor, sMessage);
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
