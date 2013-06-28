package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderDecryptedesbBean
 * @generated
 */
public interface EJSFinderDecryptedesbBean {
	/**
	 * findByLijstpositie
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Decryptedesb findByLijstpositie(java.lang.String sKieskringnummer, java.lang.String sKieslijstnummer, java.lang.String sPositienummer) throws javax.ejb.FinderException, java.rmi.RemoteException;
}
