/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KieslijstAdmin.java
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
/**
 * Remote interface for Enterprise Bean: KieslijstAdmin
 */
public interface KieslijstAdmin extends javax.ejb.EJBObject
{
	public void removeImport(int iTempID)
		throws KOAException, java.rmi.RemoteException;
	public void processImport(int iTempID)
		throws KOAException, java.rmi.RemoteException;
}