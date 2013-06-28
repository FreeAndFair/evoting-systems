package com.logicacmg.koa.kr.beans;
/**
 * Remote interface for Enterprise Bean: KRSequenceEJB
 */
public interface KRSequenceEJB extends javax.ejb.EJBObject
{
	public java.math.BigDecimal getNextID() throws java.rmi.RemoteException;
	public void setNextID(java.math.BigDecimal newNextID)
		throws java.rmi.RemoteException;
}
