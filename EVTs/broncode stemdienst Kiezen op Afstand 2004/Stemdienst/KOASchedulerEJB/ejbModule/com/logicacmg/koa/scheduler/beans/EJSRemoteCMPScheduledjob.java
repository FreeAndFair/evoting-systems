package com.logicacmg.koa.scheduler.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPScheduledjob
 * @generated
 */
public class EJSRemoteCMPScheduledjob extends EJSWrapper implements Scheduledjob {
	/**
	 * EJSRemoteCMPScheduledjob
	 * @generated
	 */
	public EJSRemoteCMPScheduledjob() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getJobtype
	 * @generated
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype getJobtype() throws java.rmi.RemoteException, javax.ejb.FinderException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.scheduler.beans.Jobtype _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getJobtype();
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
	 * getJobtypeKey
	 * @generated
	 */
	public com.logicacmg.koa.scheduler.beans.JobtypeKey getJobtypeKey() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		com.logicacmg.koa.scheduler.beans.JobtypeKey _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 1, _EJS_s);
			_EJS_result = beanRef.getJobtypeKey();
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
	 * getPriority
	 * @generated
	 */
	public java.lang.Integer getPriority() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Integer _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 2, _EJS_s);
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
			container.postInvoke(this, 2, _EJS_s);
		}
		return _EJS_result;
	}
	/**
	 * getRetrycount
	 * @generated
	 */
	public java.lang.Integer getRetrycount() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.Integer _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 3, _EJS_s);
			_EJS_result = beanRef.getRetrycount();
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
	 * getContext
	 * @generated
	 */
	public java.lang.String getContext() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 4, _EJS_s);
			_EJS_result = beanRef.getContext();
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
	 * getMessage
	 * @generated
	 */
	public java.lang.String getMessage() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 5, _EJS_s);
			_EJS_result = beanRef.getMessage();
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
	 * getStatus
	 * @generated
	 */
	public java.lang.String getStatus() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.lang.String _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 6, _EJS_s);
			_EJS_result = beanRef.getStatus();
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
	 * getLastupdate
	 * @generated
	 */
	public java.sql.Timestamp getLastupdate() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 7, _EJS_s);
			_EJS_result = beanRef.getLastupdate();
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
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
	 * getStarttime
	 * @generated
	 */
	public java.sql.Timestamp getStarttime() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 8, _EJS_s);
			_EJS_result = beanRef.getStarttime();
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
		return _EJS_result;
	}
	/**
	 * getStoptime
	 * @generated
	 */
	public java.sql.Timestamp getStoptime() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		java.sql.Timestamp _EJS_result = null;
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 9, _EJS_s);
			_EJS_result = beanRef.getStoptime();
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
		return _EJS_result;
	}
	/**
	 * privateSetJobtypeKey
	 * @generated
	 */
	public void privateSetJobtypeKey(com.logicacmg.koa.scheduler.beans.JobtypeKey inKey) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 10, _EJS_s);
			beanRef.privateSetJobtypeKey(inKey);
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
	 * secondarySetJobtype
	 * @generated
	 */
	public void secondarySetJobtype(com.logicacmg.koa.scheduler.beans.Jobtype aJobtype) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 11, _EJS_s);
			beanRef.secondarySetJobtype(aJobtype);
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
	 * setContext
	 * @generated
	 */
	public void setContext(java.lang.String newContext) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 12, _EJS_s);
			beanRef.setContext(newContext);
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
	 * setJobtype
	 * @generated
	 */
	public void setJobtype(com.logicacmg.koa.scheduler.beans.Jobtype aJobtype) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 13, _EJS_s);
			beanRef.setJobtype(aJobtype);
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
	 * setLastupdate
	 * @generated
	 */
	public void setLastupdate(java.sql.Timestamp newLastupdate) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 14, _EJS_s);
			beanRef.setLastupdate(newLastupdate);
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
	 * setMessage
	 * @generated
	 */
	public void setMessage(java.lang.String newMessage) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 15, _EJS_s);
			beanRef.setMessage(newMessage);
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
	 * setPriority
	 * @generated
	 */
	public void setPriority(java.lang.Integer newPriority) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 16, _EJS_s);
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
			container.postInvoke(this, 16, _EJS_s);
		}
		return ;
	}
	/**
	 * setRetrycount
	 * @generated
	 */
	public void setRetrycount(java.lang.Integer newRetrycount) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 17, _EJS_s);
			beanRef.setRetrycount(newRetrycount);
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
	 * setStarttime
	 * @generated
	 */
	public void setStarttime(java.sql.Timestamp newStarttime) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 18, _EJS_s);
			beanRef.setStarttime(newStarttime);
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
	/**
	 * setStatus
	 * @generated
	 */
	public void setStatus(java.lang.String newStatus) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 19, _EJS_s);
			beanRef.setStatus(newStatus);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 19, _EJS_s);
		}
		return ;
	}
	/**
	 * setStoptime
	 * @generated
	 */
	public void setStoptime(java.sql.Timestamp newStoptime) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.scheduler.beans.ScheduledjobBean beanRef = (com.logicacmg.koa.scheduler.beans.ScheduledjobBean)container.preInvoke(this, 20, _EJS_s);
			beanRef.setStoptime(newStoptime);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 20, _EJS_s);
		}
		return ;
	}
}
