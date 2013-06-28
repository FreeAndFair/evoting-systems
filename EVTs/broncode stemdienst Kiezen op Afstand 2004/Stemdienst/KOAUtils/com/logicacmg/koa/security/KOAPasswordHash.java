/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.KOAEncryptionUtil.java
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
/**
 * Utility class for encrypting a single password from the commandline
 * 
 * @author UiterliX
 */
public class KOAPasswordHash
{
	/**
	 * Method to hash a password
	 * 
	 * @param password The password to hash
	 * 
	 * @return String the hashed password
	 * 
	 * @throws Exception When something goes wrong during hashing the password.
	 * 
	 */
	public static String hashPassword(String password) throws Exception
	{
		MessageDigest md = null;
		try
		{
			md = MessageDigest.getInstance("SHA-1");
			md.update(password.getBytes());
		}
		catch (java.security.NoSuchAlgorithmException nse)
		{
			throw new Exception();
		}
		byte[] output = md.digest();
		StringBuffer sb = new StringBuffer(2 * output.length);
		for (int i = 0; i < output.length; ++i)
		{
			int k = output[i] & 0xFF;
			if (k < 0x10)
				sb.append('0');
			sb.append(Integer.toHexString(k));
		}
		return sb.toString();
	}
}