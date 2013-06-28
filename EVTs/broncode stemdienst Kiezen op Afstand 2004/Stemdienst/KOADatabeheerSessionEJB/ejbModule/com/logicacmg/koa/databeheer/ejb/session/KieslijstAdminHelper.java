/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelper.java
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
  *  1.0		09-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.ejb.session;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.koaschema.Kieslijsten;
/**
 * Remote interface for Enterprise Bean: KieslijstAdminHelper
 */
public interface KieslijstAdminHelper extends javax.ejb.EJBObject
{
	public Kieslijsten insertKieslijst(
		String kiesKringNr,
		String kieslijstNr,
		String lijstnaam)
		throws KOAException, java.rmi.RemoteException;
	public void insertLijstPostitie(
		Kieslijsten xKieslijst,
		String sPositieNr,
		String sAchternaam,
		String sVoorletters,
		String sRoepnaam,
		char sGeslacht,
		String sWoonplaats)
		throws KOAException, java.rmi.RemoteException;
}
