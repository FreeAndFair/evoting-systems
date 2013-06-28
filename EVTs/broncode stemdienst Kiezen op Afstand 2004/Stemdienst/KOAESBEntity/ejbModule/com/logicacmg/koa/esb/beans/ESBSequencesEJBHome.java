package com.logicacmg.koa.esb.beans;
/**
 * Home interface for Enterprise Bean: ESBSequencesEJB
 */
public interface ESBSequencesEJBHome extends javax.ejb.EJBHome
{
	/**
	 * Creates an instance from a key for Entity Bean: ESBSequencesEJB
	 */
	public com.logicacmg.koa.esb.beans.ESBSequencesEJB create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
	/**
	 * Finds an instance using a key for Entity Bean: ESBSequencesEJB
	 */
	public com.logicacmg.koa.esb.beans.ESBSequencesEJB findByPrimaryKey(
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey primaryKey)
		throws javax.ejb.FinderException, java.rmi.RemoteException;
}
