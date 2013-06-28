package com.logicacmg.koa.kieslijst.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessKiesLijst
 * @generated
 */
public class EJSRemoteStatelessKiesLijst extends EJSWrapper implements KiesLijst {
	/**
	 * EJSRemoteStatelessKiesLijst
	 * @generated
	 */
	public EJSRemoteStatelessKiesLijst() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getKandidaat
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.Kandidaat getKandidaat(java.lang.String sKandidaatcode) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.Kandidaat _EJS_result = null;
		try {
			com.logicacmg.koa.kieslijst.beans.KiesLijstBean beanRef = (com.logicacmg.koa.kieslijst.beans.KiesLijstBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getKandidaat(sKandidaatcode);
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
	 * verifyKandidaat
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.KandidaatResponse verifyKandidaat(java.lang.String sKandidaatcode, java.lang.String sStemcode) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.KandidaatResponse _EJS_result = null;
		try {
			com.logicacmg.koa.kieslijst.beans.KiesLijstBean beanRef = (com.logicacmg.koa.kieslijst.beans.KiesLijstBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.verifyKandidaat(sKandidaatcode, sStemcode);
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
		return _EJS_result;
	}
	/**
	 * compareKieslijstFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.dataobjects.KiesLijstFingerprintCompareResult compareKieslijstFingerprint() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.dataobjects.KiesLijstFingerprintCompareResult _EJS_result = null;
		try {
			com.logicacmg.koa.kieslijst.beans.KiesLijstBean beanRef = (com.logicacmg.koa.kieslijst.beans.KiesLijstBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.compareKieslijstFingerprint();
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
			container.postInvoke(this, 2, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getKandidaten
	 * @generated
	 */
	public java.util.Vector getKandidaten(java.lang.String sKieslijstnummer, java.lang.String sKieskringnummer) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Vector _EJS_result = null;
		try {
			com.logicacmg.koa.kieslijst.beans.KiesLijstBean beanRef = (com.logicacmg.koa.kieslijst.beans.KiesLijstBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.getKandidaten(sKieslijstnummer, sKieskringnummer);
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
			container.postInvoke(this, 3, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getPartijen
	 * @generated
	 */
	public java.util.Vector getPartijen(java.lang.String sKieskringnummer) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Vector _EJS_result = null;
		try {
			com.logicacmg.koa.kieslijst.beans.KiesLijstBean beanRef = (com.logicacmg.koa.kieslijst.beans.KiesLijstBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = beanRef.getPartijen(sKieskringnummer);
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
			container.postInvoke(this, 4, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * saveCurrentKieslijstFingerprints
	 * @generated
	 */
	public void saveCurrentKieslijstFingerprints() throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.kieslijst.beans.KiesLijstBean beanRef = (com.logicacmg.koa.kieslijst.beans.KiesLijstBean)container.preInvoke(this, 5, _EJS_s);
			beanRef.saveCurrentKieslijstFingerprints();
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
			container.postInvoke(this, 5, _EJS_s);
		}
		return ;
	}
}
