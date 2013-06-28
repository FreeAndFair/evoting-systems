package com.logicacmg.koa.scheduler.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPJobtype
 * @generated
 */
public class EJSRemoteCMPJobtype extends EJSWrapper implements Jobtype {
	/**
	 * EJSRemoteCMPJobtype
	 * @generated
	 */
	public EJSRemoteCMPJobtype() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getPriority
	 * @generated
	 */
	public java.lang.Integer getPriority() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Integer _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getPriority();
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
	 * getDefaultcontext
	 * @generated
	 */
	public java.lang.String getDefaultcontext() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getDefaultcontext();
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
	 * getImplementationclass
	 * @generated
	 */
	public java.lang.String getImplementationclass() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 2, _EJS_s);
			_EJS_result = beanRef.getImplementationclass();
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
	 * getName
	 * @generated
	 */
	public java.lang.String getName() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.getName();
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
	 * getInterval
	 * @generated
	 */
	public java.math.BigDecimal getInterval() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.math.BigDecimal _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = beanRef.getInterval();
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
	 * getSuccessor
	 * @generated
	 */
	public java.math.BigDecimal getSuccessor() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.math.BigDecimal _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 5, _EJS_s);
			_EJS_result = beanRef.getSuccessor();
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
	 * getFirsttime
	 * @generated
	 */
	public java.sql.Timestamp getFirsttime() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 6, _EJS_s);
			_EJS_result = beanRef.getFirsttime();
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
	 * getScheduledjob
	 * @generated
	 */
	public java.util.Enumeration getScheduledjob() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.util.Enumeration _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 7, _EJS_s);
			_EJS_result = beanRef.getScheduledjob();
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
	 * addScheduledjob
	 * @generated
	 */
	public void addScheduledjob(com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 8, _EJS_s);
			beanRef.addScheduledjob(aScheduledjob);
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
	 * removeScheduledjob
	 * @generated
	 */
	public void removeScheduledjob(com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 9, _EJS_s);
			beanRef.removeScheduledjob(aScheduledjob);
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
	 * secondaryAddScheduledjob
	 * @generated
	 */
	public void secondaryAddScheduledjob(com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 10, _EJS_s);
			beanRef.secondaryAddScheduledjob(aScheduledjob);
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
	 * secondaryRemoveScheduledjob
	 * @generated
	 */
	public void secondaryRemoveScheduledjob(com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 11, _EJS_s);
			beanRef.secondaryRemoveScheduledjob(aScheduledjob);
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
	 * setDefaultcontext
	 * @generated
	 */
	public void setDefaultcontext(java.lang.String newDefaultcontext) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 12, _EJS_s);
			beanRef.setDefaultcontext(newDefaultcontext);
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
	 * setFirsttime
	 * @generated
	 */
	public void setFirsttime(java.sql.Timestamp newFirsttime) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 13, _EJS_s);
			beanRef.setFirsttime(newFirsttime);
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
	 * setImplementationclass
	 * @generated
	 */
	public void setImplementationclass(java.lang.String newImplementationclass) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 14, _EJS_s);
			beanRef.setImplementationclass(newImplementationclass);
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
	 * setInterval
	 * @generated
	 */
	public void setInterval(java.math.BigDecimal newInterval) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 15, _EJS_s);
			beanRef.setInterval(newInterval);
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
	 * setName
	 * @generated
	 */
	public void setName(java.lang.String newName) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 16, _EJS_s);
			beanRef.setName(newName);
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
	/**
	 * setPriority
	 * @generated
	 */
	public void setPriority(java.lang.Integer newPriority) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 17, _EJS_s);
			beanRef.setPriority(newPriority);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 17, _EJS_s);
		}
		return ;
	}
	/**
	 * setSuccessor
	 * @generated
	 */
	public void setSuccessor(java.math.BigDecimal newSuccessor) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.JobtypeBean beanRef = (com.logicacmg.koa.scheduler.beans.JobtypeBean)container.preInvoke(this, 18, _EJS_s);
			beanRef.setSuccessor(newSuccessor);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 18, _EJS_s);
		}
		return ;
	}
}
