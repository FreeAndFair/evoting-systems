/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.FingerPrint.java
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
  *  0.1		17-04-2003	XU			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.security;
import java.security.MessageDigest;

import com.logicacmg.koa.exception.KOAException;
/**
 * Fingerprint object for creating message digests
 * on large messages
 * 
 * @author UiterliX
 */
public class FingerPrint
{
	MessageDigest md5;
	byte[] key;
	/**
	 * Constructor for the Fingerprint object
	 * 
	 * @param key Containing the key
	 * 
	 * @throws KOAException when something goes wrong getting MD5
	 * 
	 */
	public FingerPrint(String key) throws KOAException
	{
		this.key = key.getBytes();
		try
		{
			md5 = MessageDigest.getInstance("MD5");
		}
		catch (java.security.NoSuchAlgorithmException nse)
		{
			throw new KOAException("ENC-01");
		}
	}
	/**
	 * Update the messagedigest with the given byte[]
	 * 
	 * @param buffer The byte[] to update the digest with
	 */
	public void update(byte[] buffer)
	{
		md5.update(buffer);
	}
	/**
	 * Get the messagedigest
	 * 
	 * @return The messagedigest as a byte[]
	 * 
	 */
	public byte[] getDigest()
	{
		return md5.digest(key);
	}
}