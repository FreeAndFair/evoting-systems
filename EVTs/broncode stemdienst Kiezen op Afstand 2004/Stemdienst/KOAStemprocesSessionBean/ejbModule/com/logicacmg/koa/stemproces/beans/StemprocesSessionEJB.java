/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.stemproces.beans.StemprocesSessionEJB.java
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
  *  0.1		17-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.stemproces.beans;
import java.rmi.RemoteException;

import com.logicacmg.koa.dataobjects.Stem;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.exception.KOAException;
/**
 * Remote interface for Enterprise Bean: StemprocesSessionEJB
 */
public interface StemprocesSessionEJB extends javax.ejb.EJBObject
{
	/**
	 * This method handles the flow of the voting
	 * 
	 * @param Stem - This object contains data about the person a kiezer has voted for
	 * @param Kiezer - This object contains data about the kiezer
	 * 
	 * @return StemTransactie - The object contains the state of the vote
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException is htrown whem something has gone wrong.
	 */
	public StemTransactie vote(
		Stem xStem,
		String sStemcode,
		String sWachtwoord)
		throws KOAException, RemoteException;
	/**
	 * This method returns the next transactioncode.
	 * 
	 * @return String the transactioncode
	 * @throws KOAException when it failed to get the next transactioncode
	 */
	public String getNextTransactionCode()
		throws KOAException, RemoteException;
}
