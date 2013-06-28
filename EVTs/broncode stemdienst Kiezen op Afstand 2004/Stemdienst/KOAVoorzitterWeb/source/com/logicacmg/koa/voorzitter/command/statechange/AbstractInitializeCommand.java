/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.InitializeCommand.java
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
  *  0.1		01-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.voorzitter.command.statechange;
import java.io.InputStream;
import java.security.PublicKey;
import java.util.Iterator;

import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.security.KOAKeyPair;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.voorzitter.command.statechange.AbstractStateChangeCommand;
public abstract class AbstractInitializeCommand
	extends AbstractStateChangeCommand
{
	public final static String PUBLIC_KEY_NAME = "publickey";
	public final static String PASSWORD_NAME = "password";
	protected PublicKey g_pkPublicKey = null;
	/**
	 * Static to ensure the preloading of the sun crypto provider
	 */
	static {
		java.security.Security.addProvider(
			new com.sun.crypto.provider.SunJCE());
	}
	/**
	 * Initialises the command. Here the parameters are
	 * extracted from the request.
	 *
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * 
	 * @throws EPlatformException	thrown when something goes wrong with reading the data
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[InitializeCommand] init");
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[InitializeCommand.init] Start loading the public key ");
			Iterator xIter = getFileItem(request);
			FileItem xTemp = null;
			FileItem xPublicKey = null;
			FileItem xPassword = null;
			/* get the right params */
			while (xIter.hasNext())
			{
				xTemp = (FileItem) xIter.next();
				/* store pincode1 */
				if (xTemp.getFieldName().equals("pincode1"))
				{
					sPincode1 = xTemp.getString();
				}
				/* store pincode2 */
				if (xTemp.getFieldName().equals("pincode2"))
				{
					sPincode2 = xTemp.getString();
				}
				/* store the public key */
				if (xTemp.getFieldName().equals(PUBLIC_KEY_NAME))
				{
					xPublicKey = xTemp;
				}
				/* store the password */
				if (xTemp.getFieldName().equals(PASSWORD_NAME))
				{
					xPassword = xTemp;
				}
			}
			if (xPublicKey == null || xPassword == null)
			{
				// param is not found in the request
				throw new KOAException(ErrorConstants.VALIDATE_PUBLIC_KEY);
			}
			g_pkPublicKey =
				parsePublicKey(
					xPublicKey.getInputStream(),
					xPassword.getString());
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[InitializeCommand.init] Public Key file parsed, got public key...");
		}
		catch (java.io.IOException ioe)
		{
			String[] params = { "Input Stream" };
			KOALogHelper.logErrorCode(
				"InitializeCommand.init",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.COMMAND_INITIALIZE_INIT, ioe);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"InitializeCommand.init",
				"KOA Exception during initialize of the command",
				koae);
			throw koae;
		}
	}
	/**
	 * parse the input stream to the public key using the 
	 * password in the decryption.
	 * 
	 * @param InputStream The inputstream to parse
	 * @param String	  The password to use in the decryption
	 * 
	 * @return PublicKey the public key
	 * 
	 * @throws KOAException Exception when something goes wrong during parsing.
	 */
	private PublicKey parsePublicKey(InputStream is, String sPassword)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[InitializeCommand.parsePublicKey] Start parsing the public key");
		PublicKey pkKey = null;
		try
		{
			KOAKeyPair xKeyPair =
				new KOAKeyPair(sPassword, is, KOAKeyPair.PUBLIC_KEY);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[InitializeCommand.parsePublicKey] parsing complete returning public key");
			pkKey = xKeyPair.getPublicKey();
		}
		catch (KOAException koae)
		{
			/* Log the error in public key saving for monitor by tivoli */
			String[] params = { "public" };
			KOALogHelper.logErrorCode(
				"InitializeCommand.parsePublicKey",
				ErrorConstants.ERR_PARSE_PUB_PRIVKEY,
				params,
				koae);
			KOALogHelper.logError(
				"InitializeCommand.parsePublicKey",
				"Problems validating the public key",
				koae);
			throw new KOAException(ErrorConstants.VALIDATE_PUBLIC_KEY, koae);
		}
		return pkKey;
	}
}