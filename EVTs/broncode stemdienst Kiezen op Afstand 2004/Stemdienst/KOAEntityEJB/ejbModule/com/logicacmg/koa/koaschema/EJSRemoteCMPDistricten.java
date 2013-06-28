package com.logicacmg.koa.koaschema;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPDistricten
 * @generated
 */
public class EJSRemoteCMPDistricten extends EJSWrapper implements Districten {
	/**
	 * EJSRemoteCMPDistricten
	 * @generated
	 */
	public EJSRemoteCMPDistricten() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getFk_dist_kkr
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieskringen getFk_dist_kkr() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.Kieskringen _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getFk_dist_kkr();
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
			container.postInvoke(this, 0, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getFk_dist_kkrKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey getFk_dist_kkrKey() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.koaschema.KieskringenKey _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getFk_dist_kkrKey();
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
	 * getDistrictnaam
	 * @generated
	 */
	public java.lang.String getDistrictnaam() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.getDistrictnaam();
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
	 * privateSetFk_dist_kkrKey
	 * @generated
	 */
	public void privateSetFk_dist_kkrKey(com.logicacmg.koa.koaschema.KieskringenKey inKey) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 3, _EJS_s);
			beanRef.privateSetFk_dist_kkrKey(inKey);
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
		return ;
	}
	/**
	 * secondarySetFk_dist_kkr
	 * @generated
	 */
	public void secondarySetFk_dist_kkr(com.logicacmg.koa.koaschema.Kieskringen aFk_dist_kkr) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 4, _EJS_s);
			beanRef.secondarySetFk_dist_kkr(aFk_dist_kkr);
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
		return ;
	}
	/**
	 * setDistrictnaam
	 * @generated
	 */
	public void setDistrictnaam(java.lang.String newDistrictnaam) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 5, _EJS_s);
			beanRef.setDistrictnaam(newDistrictnaam);
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
	/**
	 * setFk_dist_kkr
	 * @generated
	 */
	public void setFk_dist_kkr(com.logicacmg.koa.koaschema.Kieskringen aFk_dist_kkr) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.koaschema.DistrictenBean beanRef = (com.logicacmg.koa.koaschema.DistrictenBean)container.preInvoke(this, 6, _EJS_s);
			beanRef.setFk_dist_kkr(aFk_dist_kkr);
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
		return ;
	}
}
