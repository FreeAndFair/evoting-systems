package com.logicacmg.koa.sar;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderSarBean
 * @generated
 */
public interface EJSFinderSarBean {
	/**
	 * findByStemcode
	 * @generated
	 */
	public com.logicacmg.koa.sar.Sar findByStemcode(java.lang.String sStemcode) throws javax.ejb.FinderException, java.rmi.RemoteException;
}
