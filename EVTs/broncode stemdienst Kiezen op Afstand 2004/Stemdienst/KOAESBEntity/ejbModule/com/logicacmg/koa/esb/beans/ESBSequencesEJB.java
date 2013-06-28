package com.logicacmg.koa.esb.beans;
/**
 * Remote interface for Enterprise Bean: ESBSequencesEJB
 */
public interface ESBSequencesEJB extends javax.ejb.EJBObject
{
	public java.math.BigDecimal getNextID() throws java.rmi.RemoteException;
	public void setNextID(java.math.BigDecimal newNextID)
		throws java.rmi.RemoteException;
}
