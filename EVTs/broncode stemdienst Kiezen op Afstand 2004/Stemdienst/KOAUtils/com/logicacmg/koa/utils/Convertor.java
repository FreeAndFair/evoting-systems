/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.utils.Convertor.java
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
  *  0.1		17-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.utils;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.util.Enumeration;
import java.util.StringTokenizer;
import java.util.Vector;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.security.KOAKeyPair;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class responsible for convertions between data types.
 * 
 * @author KuijerM
 */
public class Convertor
{
	/**
	 * Always preload the security provider
	 */
	static {
		java.security.Security.addProvider(
			new com.sun.crypto.provider.SunJCE());
	}
	/**
	 * Convertor method to convert a publicKey to
	 * a byte array.
	 * 
	 * @param PublicKey the public key to convert
	 * 
	 * @return byte [] containing the byte representation of the public key
	 * 
	 * @throws KOAException Exception when something goes wrong during convertion
	 */
	public byte[] publicKeyToByteArray(PublicKey pkPublicKey)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[Convertor.publicKeyToByteArray] Converting public key to byte array");
		return this.objectToByteArray(pkPublicKey);
	}
	/**
	 * Convertor method to convert a byte array to
	 * a Public key.
	 * 
	 * @param byte[] containing the byte representation of the public key to convert
	 *  
	 * @return PublicKey the public key created from the bytes
	 * 
	 * @throws KOAException Exception when something goes wrong during convertion
	 */
	public PublicKey byteArrayToPublicKey(byte[] baBytes) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[Convertor.byteArrayToPublicKey] Converting byte array to public key");
		/* init variables */
		PublicKey pkPublicKey = null;
		try
		{
			/* get the result and cast it to the private key */
			pkPublicKey = (PublicKey) this.byteArrayToObject(baBytes);
		}
		catch (ClassCastException cce)
		{
			String[] params = { "public key" };
			KOALogHelper.logErrorCode(
				"Convertor.byteArrayToPublicKey",
				ErrorConstants.ERR_CONVERTOR_CONVERT_BYTE_TO_OBJECT,
				cce);
			throw new KOAException(ErrorConstants.CONVERTOR_PUBL_KEY, cce);
		}
		return pkPublicKey;
	}
	/**
	 * Convertor method to convert a byte array to
	 * a Private key.
	 * 
	 * @param byte[] containing the byte representation of the private key to convert
	 * @param String The password used to encrypt the private key 
	 * 
	 * @return PrivateKey the private key created from the bytes
	 * 
	 * @throws KOAException Exception when something goes wrong during convertion
	 */
	public PrivateKey byteArrayToPrivateKey(byte[] baBytes, String sPassword)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[Convertor.byteArrayToPrivateKey] Converting byte array to private key");
		/* init variables */
		PrivateKey pkPrivateKey = null;
		try
		{
			InputStream is = new ByteArrayInputStream(baBytes);
			KOAKeyPair xKeyPair =
				new KOAKeyPair(sPassword, is, KOAKeyPair.PRIVATE_KEY);
			/* get the result and cast it to the private key */
			pkPrivateKey = xKeyPair.getPrivateKey();
		}
		catch (Exception e)
		{
			String[] params = { "private key" };
			KOALogHelper.logErrorCode(
				"Convertor.byteArrayToPrivateKey",
				ErrorConstants.ERR_CONVERTOR_CONVERT_BYTE_TO_OBJECT,
				params,
				e);
			throw new KOAException(ErrorConstants.CONVERTOR_PRIV_KEY, e);
		}
		return pkPrivateKey;
	}
	/**
	 * Convertor method to convert a object to
	 * a byte array.
	 * 
	 * @param Object	the object to convert
	 * 
	 * @return byte[]	containing the byte representation of the object
	 * 
	 * @throws KOAException Exception when something goes wrong during convertion
	 */
	private byte[] objectToByteArray(Object obj) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[Convertor.objectToByteArray] Converting object to byte array");
		/* init variables */
		byte[] baBytes = new byte[0];
		ByteArrayOutputStream baosOut = null;
		ObjectOutputStream oosOut = null;
		try
		{
			/* create outputstreams */
			baosOut = new ByteArrayOutputStream();
			oosOut = new ObjectOutputStream(baosOut);
			/* write the object to the object outputstream */
			oosOut.writeObject(obj);
			/* get the bytes */
			baBytes = baosOut.toByteArray();
		}
		catch (IOException ioe)
		{
			String[] params = { "object" };
			KOALogHelper.logErrorCode(
				"Convertor.objectToByteArray",
				ErrorConstants.ERR_CONVERTOR_CONVERT_OBJECT_TO_BYTE,
				params,
				ioe);
			throw new KOAException(ErrorConstants.CONVERTOR_OBJ_BYTE, ioe);
		}
		finally
		{
			if (oosOut != null)
			{
				try
				{
					oosOut.close();
				}
				catch (Exception e)
				{
					KOALogHelper.logErrorCode(
						"Convertor.objectToByteArray",
						ErrorConstants.ERR_CLOSE_STREAM,
						e);
				}
			}
			if (baosOut != null)
			{
				try
				{
					baosOut.close();
				}
				catch (Exception e)
				{
					KOALogHelper.logErrorCode(
						"Convertor.objectToByteArray",
						ErrorConstants.ERR_CLOSE_STREAM,
						e);
				}
			}
		}
		return baBytes;
	}
	/**
	 * Convertor method to convert a byte array to an object.
	 * 
	 * @param byte[]	containing the byte representation of the object to convert
	 *  
	 * @return Object 	the object created from the bytes
	 * 
	 * @throws KOAException Exception when something goes wrong during convertion
	 */
	private Object byteArrayToObject(byte[] baBytes) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[Convertor.byteArrayToObject] Converting byte array to object");
		/* init variables */
		Object obj = null;
		ByteArrayInputStream baisIn = null;
		ObjectInputStream oisIn = null;
		try
		{
			/* create inputstreams */
			baisIn = new ByteArrayInputStream(baBytes);
			oisIn = new ObjectInputStream(baisIn);
			/* read the object from the input stream */
			obj = oisIn.readObject();
		}
		catch (IOException ioe)
		{
			KOALogHelper.logError(
				"Convertor.byteArrayToObject",
				"Problems converting byte array to object",
				ioe);
			throw new KOAException(ErrorConstants.CONVERTOR_BYTE_OBJ, ioe);
		}
		catch (ClassNotFoundException cnfe)
		{
			KOALogHelper.logError(
				"Convertor.byteArrayToObject",
				"Class not found exception",
				cnfe);
			throw new KOAException(ErrorConstants.CONVERTOR_BYTE_OBJ, cnfe);
		}
		finally
		{
			if (oisIn != null)
			{
				try
				{
					oisIn.close();
				}
				catch (Exception e)
				{
					KOALogHelper.logError(
						"Convertor.byteArrayToObject",
						"Could not close the object output stream",
						e);
				}
			}
			if (baisIn != null)
			{
				try
				{
					baisIn.close();
				}
				catch (Exception e)
				{
					KOALogHelper.logError(
						"Convertor.byteArrayToObject",
						"Could not close the byte array output stream",
						e);
				}
			}
		}
		return obj;
	}
	/**
	 * Convert a tokenized string to an enumeration of
	 * String that were tokenized. 
	 * 
	 * @param String The string to unwrap
	 * @param String The token
	 * 
	 * @return Enumeration containing all the Strings
	 */
	public Enumeration tokenizedStringToEnumeration(
		String sString,
		String sSeperatorToken)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[Convertor.tokenizedStringToEnumeration] Using token : "
				+ sSeperatorToken
				+ " Converting string : "
				+ sString);
		/* init variables */
		Vector vSeperatedStrings = new Vector();
		StringTokenizer stTokenizer =
			new StringTokenizer(sString, sSeperatorToken);
		String sElement = null;
		/* loop through the string tokenizer */
		while (stTokenizer.hasMoreElements())
		{
			sElement = stTokenizer.nextToken();
			/* if it is not an empty string, add it */
			if (!sElement.equals(""))
			{
				vSeperatedStrings.add(sElement);
			}
		}
		/* return the enumeration */
		return vSeperatedStrings.elements();
	}
}