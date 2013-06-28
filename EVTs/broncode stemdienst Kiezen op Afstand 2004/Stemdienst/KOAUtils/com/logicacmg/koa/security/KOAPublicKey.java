/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.KOAPublicKey.java
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
package com.logicacmg.koa.security;
import java.rmi.RemoteException;
import java.security.PublicKey;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Singleton class that contains the public key 
 * for the KOA System. This singleton will get its 
 * public key at the controller.
 * 
 * @author KuijerM
 */
public class KOAPublicKey
{
	/**
	 * The singleton instance of the koa public key class
	 * 
	 */
	private static KOAPublicKey g_xInstance = null;
	/**
	 * The public key provided by the controller
	 * 
	 */
	private PublicKey g_pkPublicKey = null;
	/**
	 * gets the singleton instance of the KOAPublicKey class.
	 * 
	 * @return KOAPublicKey the instance of the class
	 * 
	 * @throws KOAException Exception when something goes wrong getting the instance
	 * 
	 */
	private static KOAPublicKey getInstance() throws KOAException
	{
		/* check if there is an instance and a public key */
		if (g_xInstance == null || g_xInstance.g_pkPublicKey == null)
		{
			/* create new instance when one of the two checks is false */
			g_xInstance = new KOAPublicKey();
		}
		/* return the instance */
		return g_xInstance;
	}
	/**
	 * Private constructor for the KOAPublicKey class.
	 * 
	 * @throws KOAException When something goes wrong loading the public key
	 * 
	 */
	private KOAPublicKey() throws KOAException
	{
		/* load the public key */
		this.loadPublicKey();
	}
	/**
	 * loads the public key.
	 * The public key is provided by the controller.
	 * 
	 * @throws KOAException when someting goes wrong loading the public key
	 * 
	 */
	private void loadPublicKey() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAPublicKey.loadPublicKey] loading public key from controller");
		/* set the propeties for the initial context */
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
		try
		{
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* look up the home interface */
			Object obj =
				icContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			ControllerHome xControllerHome =
				(ControllerHome) PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			/* create remote instance from the home interface */
			Controller xController = xControllerHome.create();
			/* get public key */
			g_pkPublicKey = xController.getPublicKey();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAPublicKey.loadPublicKey] got public key ");
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"KOAPublicKey.loadPublicKey",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.SECURITY_PUBLICKEY_LOAD, ce);
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"KOAPublicKey.loadPublicKey",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(ErrorConstants.SECURITY_PUBLICKEY_LOAD, ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"KOAPublicKey.loadPublicKey",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.SECURITY_PUBLICKEY_LOAD, re);
		}
	}
	/**
	 * Only public method on this class to get the public key
	 * There is only one public key for the KOA application.
	 * 
	 * @throws KOAException When something goes wrong getting the public key
	 */
	public static synchronized PublicKey getPublicKey() throws KOAException
	{
		return getInstance().g_pkPublicKey;
	}
}