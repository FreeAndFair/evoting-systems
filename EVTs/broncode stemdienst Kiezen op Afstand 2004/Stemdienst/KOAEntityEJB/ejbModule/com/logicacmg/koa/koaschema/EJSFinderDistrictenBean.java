package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderDistrictenBean
 * @generated
 */
public interface EJSFinderDistrictenBean {
	/**
	 * findDistrictenByFk_dist_kkr
	 * @generated
	 */
	public EJSFinder findDistrictenByFk_dist_kkr(com.logicacmg.koa.koaschema.KieskringenKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException;
}
