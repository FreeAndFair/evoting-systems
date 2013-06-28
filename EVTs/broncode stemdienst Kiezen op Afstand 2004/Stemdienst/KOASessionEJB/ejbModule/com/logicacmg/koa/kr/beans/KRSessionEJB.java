/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.kr.beans.KRSessionEJB
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
  *  0.1		11-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.kr.beans;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.dataobjects.Kiezer;
import com.logicacmg.koa.dataobjects.StemTransactie;
/**
 * Remote interface for Enterprise Bean: KRSessionEJB
 */
public interface KRSessionEJB extends javax.ejb.EJBObject
{
	/**
	     *  This method performs action when the system state is going to be changed.
	     * 
	     *  Note: The system isn't in the new state yet, this method performs the actions needed
	     *        for the transition to the new state! 
	     * 
	     * @param sCurrentState The current state the system is in
	     * @param newState int Indication of the new system state. 
	     *                     (The value comes from the SystemState class)
	     * 
	     * @return CallResult object that contains the result of the performed actions.
	     */
	public void changeState(String sCurrentState, String sNewState)
		throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException;
	public String getCurrentSystemState()
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	public StemTransactie verifyKiezer(
		String sStemcode,
		String sWachtwoord,
		String sModaliteit,
		boolean bUpdateCounters)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	/**
	 * This method marks a kiezer as already voted
	 * 
	 * Note: This method has to be configured to participate in a exitsing tranmsaction
	 * 
	 * @param sStemcode - the Stemcode of tje kiezer to be marked as already voted
	 * 
	 */
	public void kiezerHeeftGestemd(Kiezer xKiezer)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	public CounterData collectCounters(String sComponentID)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	public void emptyKR()
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	public Kiezer getKiezer(String sStemcode)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
}
