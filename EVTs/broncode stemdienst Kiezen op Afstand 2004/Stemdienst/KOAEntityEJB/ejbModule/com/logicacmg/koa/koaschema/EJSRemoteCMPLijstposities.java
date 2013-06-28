package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPLijstposities
 * @generated
 */
public class EJSRemoteCMPLijstposities extends EJSWrapper implements Lijstposities {
	/**
	 * EJSRemoteCMPLijstposities
	 * @generated
	 */
	public EJSRemoteCMPLijstposities() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getGeslacht
	 * @generated
	 */
	public char getGeslacht() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		char _EJS_result = '\u0000';
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getGeslacht();
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
	 * getFk_klkr_1
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieslijsten getFk_klkr_1() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.Kieslijsten _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getFk_klkr_1();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
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
	 * getFk_klkr_1Key
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.KieslijstenKey getFk_klkr_1Key() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.KieslijstenKey _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.getFk_klkr_1Key();
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
	 * getAchternaam
	 * @generated
	 */
	public java.lang.String getAchternaam() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.getAchternaam();
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
	 * getRoepnaam
	 * @generated
	 */
	public java.lang.String getRoepnaam() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = beanRef.getRoepnaam();
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
	 * getVoorletters
	 * @generated
	 */
	public java.lang.String getVoorletters() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 5, _EJS_s);
			_EJS_result = beanRef.getVoorletters();
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
		return _EJS_result;
	}
	/**
	 * getWoonplaats
	 * @generated
	 */
	public java.lang.String getWoonplaats() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 6, _EJS_s);
			_EJS_result = beanRef.getWoonplaats();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 6, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getKandidaatcodes
	 * @generated
	 */
	public java.util.Enumeration getKandidaatcodes() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Enumeration _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 7, _EJS_s);
			_EJS_result = beanRef.getKandidaatcodes();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (javax.ejb.FinderException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 7, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * addKandidaatcodes
	 * @generated
	 */
	public void addKandidaatcodes(com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 8, _EJS_s);
			beanRef.addKandidaatcodes(aKandidaatcodes);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 8, _EJS_s);
		}
		return ;
	}
	/**
	 * removeKandidaatcodes
	 * @generated
	 */
	public void removeKandidaatcodes(com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 9, _EJS_s);
			beanRef.removeKandidaatcodes(aKandidaatcodes);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 9, _EJS_s);
		}
		return ;
	}
	/**
	 * secondaryAddKandidaatcodes
	 * @generated
	 */
	public void secondaryAddKandidaatcodes(com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 10, _EJS_s);
			beanRef.secondaryAddKandidaatcodes(aKandidaatcodes);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 10, _EJS_s);
		}
		return ;
	}
	/**
	 * secondaryRemoveKandidaatcodes
	 * @generated
	 */
	public void secondaryRemoveKandidaatcodes(com.logicacmg.koa.koaschema.Kandidaatcodes aKandidaatcodes) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 11, _EJS_s);
			beanRef.secondaryRemoveKandidaatcodes(aKandidaatcodes);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 11, _EJS_s);
		}
		return ;
	}
	/**
	 * setAchternaam
	 * @generated
	 */
	public void setAchternaam(java.lang.String newAchternaam) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 12, _EJS_s);
			beanRef.setAchternaam(newAchternaam);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 12, _EJS_s);
		}
		return ;
	}
	/**
	 * setGeslacht
	 * @generated
	 */
	public void setGeslacht(char newGeslacht) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 13, _EJS_s);
			beanRef.setGeslacht(newGeslacht);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 13, _EJS_s);
		}
		return ;
	}
	/**
	 * setRoepnaam
	 * @generated
	 */
	public void setRoepnaam(java.lang.String newRoepnaam) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 14, _EJS_s);
			beanRef.setRoepnaam(newRoepnaam);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 14, _EJS_s);
		}
		return ;
	}
	/**
	 * setVoorletters
	 * @generated
	 */
	public void setVoorletters(java.lang.String newVoorletters) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 15, _EJS_s);
			beanRef.setVoorletters(newVoorletters);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 15, _EJS_s);
		}
		return ;
	}
	/**
	 * setWoonplaats
	 * @generated
	 */
	public void setWoonplaats(java.lang.String newWoonplaats) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.LijstpositiesBean beanRef = (com.logicacmg.koa.koaschema.LijstpositiesBean)container.preInvoke(this, 16, _EJS_s);
			beanRef.setWoonplaats(newWoonplaats);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 16, _EJS_s);
		}
		return ;
	}
}
