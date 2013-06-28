package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderLijstpositiesBean
 * @generated
 */
public interface EJSFinderLijstpositiesBean {
	/**
	 * findLijstpositiesByFk_klkr_1
	 * @generated
	 */
	public EJSFinder findLijstpositiesByFk_klkr_1(com.logicacmg.koa.koaschema.KieslijstenKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException;
}
