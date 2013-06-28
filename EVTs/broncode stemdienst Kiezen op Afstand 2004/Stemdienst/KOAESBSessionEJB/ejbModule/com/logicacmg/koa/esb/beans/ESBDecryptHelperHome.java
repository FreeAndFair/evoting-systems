package com.logicacmg.koa.esb.beans;

import com.logicacmg.koa.esb.beans.ESBDecryptHelper;

/**
 * Home interface for Enterprise Bean: ESBDecryptHelper
 */
public interface ESBDecryptHelperHome extends javax.ejb.EJBHome
{
	/**
	 * Creates a default instance of Session Bean: ESBDecryptHelper
	 */
	public ESBDecryptHelper create()
		throws javax.ejb.CreateException, java.rmi.RemoteException;
}
