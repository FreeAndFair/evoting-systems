package com.logicacmg.koa.scheduler.beans;
/**
 * Remote interface for Enterprise Bean: Scheduledjob
 */
public interface Scheduledjob extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: starttime
	 */
	public java.sql.Timestamp getStarttime() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: starttime
	 */
	public void setStarttime(java.sql.Timestamp newStarttime)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: stoptime
	 */
	public java.sql.Timestamp getStoptime() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: stoptime
	 */
	public void setStoptime(java.sql.Timestamp newStoptime)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: priority
	 */
	public java.lang.Integer getPriority() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: priority
	 */
	public void setPriority(java.lang.Integer newPriority)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: status
	 */
	public java.lang.String getStatus() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: status
	 */
	public void setStatus(java.lang.String newStatus)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: retrycount
	 */
	public java.lang.Integer getRetrycount() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: retrycount
	 */
	public void setRetrycount(java.lang.Integer newRetrycount)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: lastupdate
	 */
	public java.sql.Timestamp getLastupdate() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: lastupdate
	 */
	public void setLastupdate(java.sql.Timestamp newLastupdate)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: context
	 */
	public java.lang.String getContext() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: context
	 */
	public void setContext(java.lang.String newContext)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: message
	 */
	public java.lang.String getMessage() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: message
	 */
	public void setMessage(java.lang.String newMessage)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondarySetJobtype(
		com.logicacmg.koa.scheduler.beans.Jobtype aJobtype)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void setJobtype(com.logicacmg.koa.scheduler.beans.Jobtype aJobtype)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.scheduler.beans.JobtypeKey getJobtypeKey()
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetJobtypeKey(
		com.logicacmg.koa.scheduler.beans.JobtypeKey inKey)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named jobtype.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype getJobtype()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
}
