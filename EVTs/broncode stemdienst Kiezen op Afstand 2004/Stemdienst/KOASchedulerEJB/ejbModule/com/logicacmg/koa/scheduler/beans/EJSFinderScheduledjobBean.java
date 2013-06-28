package com.logicacmg.koa.scheduler.beans;
import com.ibm.ejs.persistence.EJSFinder;
import javax.ejb.FinderException;
import java.rmi.RemoteException;
/**
 * EJSFinderScheduledjobBean
 * @generated
 */
public interface EJSFinderScheduledjobBean {
	/**
	 * findScheduledjobByJobtype
	 * @generated
	 */
	public EJSFinder findScheduledjobByJobtype(com.logicacmg.koa.scheduler.beans.JobtypeKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException;
}
