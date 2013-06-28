/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.EncryptedStem.java
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
package com.logicacmg.koa.dataobjects;
/**
 * this class contains a encrypted version of a vote
 */
public class EncryptedStem implements java.io.Serializable
{
	public String stemcode;
	public byte[] encryptedVote;
}
