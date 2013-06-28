/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.esb.beans.ESBSessionEJB
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
  *  0.1		14-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.esb.beans;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.dataobjects.EncryptedStem;
/**
 * Remote interface for Enterprise Bean: KOAESBSessionEJB
 */
public interface ESBSessionEJB extends javax.ejb.EJBObject
{
	/**
	 *  This method performs action when the system state is going to be changed.
	 * 
	 *  Note: The system isn't in the new state yet, this method performs the actions needed
	 *        for the transition to the new state! 
	 * 
	 * @param newState int Indication of the new system state. 
	 *                     (The value comes from the SystemState class)
	 * 
	 * @return CallResult object that contains the result of the performed actions.
	 */
	public void changeState(String sCurrentState, String sNewState)
		throws java.rmi.RemoteException, com.logicacmg.koa.exception.KOAException;
	public CounterData collectCounters(String sComponentID)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	public void saveEncryptedVote(EncryptedStem xEncryptedStem)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	/**
	 * This method decrypts the data in the ESB and places the decrypted result 
	 * in a other table.
	 * 
	 * @param xPrivateKey The private key of the chairmn to encrypt the data.
	 * @param sPassword The password used to encrypt the private key
	 * 
	 */
	public void openESB(byte[] baPrivateKey, String sPassword)
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	/**
	 * This method counts the votes stored in the decrypted ESB table and places 
	 * the result in XML format in the ... table
	 * 
	 */
	public void telStemmen()
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
	public void emptyESB()
		throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException;
}
