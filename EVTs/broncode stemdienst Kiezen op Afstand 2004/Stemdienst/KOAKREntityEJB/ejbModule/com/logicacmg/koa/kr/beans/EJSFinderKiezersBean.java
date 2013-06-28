package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderKiezersBean
 * @generated
 */
public interface EJSFinderKiezersBean {
	/**
	 * findByKiezerId
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByKiezerId(java.lang.String sKiezerId) throws javax.ejb.FinderException, java.rmi.RemoteException;
}
