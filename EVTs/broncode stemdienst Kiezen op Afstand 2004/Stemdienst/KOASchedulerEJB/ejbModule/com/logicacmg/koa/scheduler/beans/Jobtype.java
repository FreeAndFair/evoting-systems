package com.logicacmg.koa.scheduler.beans;
/**
 * Remote interface for Enterprise Bean: Jobtype
 */
public interface Jobtype extends javax.ejb.EJBObject
{
	/**
	 * Get accessor for persistent attribute: name
	 */
	public java.lang.String getName() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: name
	 */
	public void setName(java.lang.String newName)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: firsttime
	 */
	public java.sql.Timestamp getFirsttime() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: firsttime
	 */
	public void setFirsttime(java.sql.Timestamp newFirsttime)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: interval
	 */
	public java.math.BigDecimal getInterval() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: interval
	 */
	public void setInterval(java.math.BigDecimal newInterval)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: successor
	 */
	public java.math.BigDecimal getSuccessor() throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: successor
	 */
	public void setSuccessor(java.math.BigDecimal newSuccessor)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: implementationclass
	 */
	public java.lang.String getImplementationclass()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: implementationclass
	 */
	public void setImplementationclass(java.lang.String newImplementationclass)
		throws java.rmi.RemoteException;
	/**
	 * Get accessor for persistent attribute: defaultcontext
	 */
	public java.lang.String getDefaultcontext()
		throws java.rmi.RemoteException;
	/**
	 * Set accessor for persistent attribute: defaultcontext
	 */
	public void setDefaultcontext(java.lang.String newDefaultcontext)
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
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryAddScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void secondaryRemoveScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public java.util.Enumeration getScheduledjob()
		throws java.rmi.RemoteException, javax.ejb.FinderException;
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void addScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException;
	/**
	 * This method was generated for supporting the association named scheduledjob.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void removeScheduledjob(
		com.logicacmg.koa.scheduler.beans.Scheduledjob aScheduledjob)
		throws java.rmi.RemoteException;
}
