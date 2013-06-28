/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelper.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		09-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.ejb.session;
import com.logicacmg.koa.databeheer.data.KiezerData;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kr.beans.KiezersHome;
import com.logicacmg.koa.sar.SarHome;
/**
 * Remote interface for Enterprise Bean: KiesRegisterAdminHelper
 */
public interface KiesRegisterAdminHelper extends javax.ejb.EJBObject
{
	public String[] insertKiezers(
		KiezerData[] kiezers,
		KiezersHome xKiezersHome,
		SarHome xSarHome)
		throws KOAException, java.rmi.RemoteException;
	/**
	 * update a list of kiezers in the database
	 * 
	 * @param xKiezers List of kiezers 
	 * @param xKiezersHome reference to kiezers home interface (this is for performance resons)
	 * @param xSarHome reference to sar home interface (this is for performance resons)
	 * @return String[] Array of kiezers id's that are already in the kiezers table
	 */
	public String[] updateKiezers(
		KiezerData[] xKiezers,
		KiezersHome xKiezersHome,
		SarHome xSarHome)
		throws KOAException, java.rmi.RemoteException;
	/**
	 * set a kiezer removed in the database
	 * 
	 * @param sKiezerId kiezerID
	 * @return String returns null if OK else it returns the reason wy its is not removed
	 */
	public String removeKiezer(String sKiezerId)
		throws KOAException, java.rmi.RemoteException;
}
