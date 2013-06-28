/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.CountVoteCommand.java
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
import java.rmi.RemoteException;
import java.security.PrivateKey;
import java.util.Hashtable;
import java.util.Iterator;
import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.Convertor;
import com.logicacmg.koa.utils.KOALogHelper;
import com
	.logicacmg
	.koa
	.voorzitter
	.command
	.statechange
	.AbstractStateChangeCommand;
/**
 * Change state to vote count.
 * 
 * @author KuijerM
 * 
 */
public class PrepareVoteCountCommand extends AbstractStateChangeCommand
{
	public final static String PRIVATE_KEY_NAME = "privatekey";
	public final static String PASSWORD_NAME = "password";
	private byte[] g_baPrivateKey = null;
	private String g_sPassword = null;
	/**
	 * The execute method on the PrepareVoteCount command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of the Controller can not be created.
	 */
	public void execute()
		throws com.logica.eplatform.command.CommandException, EPlatformException
	{
		LogHelper.log(LogHelper.INFO, "[prepareVoteCount] execute ");
		try
		{
			// init the variabeles 
			Hashtable htProps = new Hashtable();
			htProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
			htProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
			// init the context 
			InitialContext icContext = new InitialContext(htProps);
			// lookup the controller 
			Object obj =
				icContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			// create the controller 
			ControllerHome xControllerHome =
				(ControllerHome) PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			Controller xController = xControllerHome.create();
			xController = xControllerHome.create();
			// Verify pincodes. If validated then continue with change of state 
			g_crCallResult = xController.checkPinCode(sPincode1, sPincode2);
			if (g_crCallResult.getResult() == g_crCallResult.RESULT_OK)
			{
				// store the private Key 
				g_crCallResult =
					xController.prepareVoteCount(g_baPrivateKey, g_sPassword);
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"prepareVoteCount.execute",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOAException(ErrorConstants.COMMAND_COUNTVOTE_EXEC, ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"prepareVoteCount.execute",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.COMMAND_COUNTVOTE_EXEC, re);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"prepareVoteCount.execute",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.COMMAND_COUNTVOTE_EXEC, ce);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"prepareVoteCount.execute",
				"KOAException while saving the private key",
				koae);
			throw koae;
		}
	}
	/**
	 * Initialises the command. Here the parameters are
	 * extracted from the request.
	 *
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * 
	 * @throws EPlatformException	necessary to fullfill abstract method signature
	 */
	public void init(HttpServletRequest request) throws EPlatformException
	{
		LogHelper.trace(LogHelper.TRACE, "[prepareVoteCount] init");
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[prepareVoteCount.init] Start loading the private key ");
			Iterator xIter = getFileItem(request);
			FileItem xTemp = null;
			FileItem xPrivateKey = null;
			FileItem xPassword = null;
			// get the right params 
			while (xIter.hasNext())
			{
				xTemp = (FileItem) xIter.next();
				// store pincode1 
				if (xTemp.getFieldName().equals("pincode1"))
				{
					sPincode1 = xTemp.getString();
				}
				// store pincode2
				if (xTemp.getFieldName().equals("pincode2"))
				{
					sPincode2 = xTemp.getString();
				}
				// store the private key 
				if (xTemp.getFieldName().equals(PRIVATE_KEY_NAME))
				{
					xPrivateKey = xTemp;
				}
				// store the password 
				if (xTemp.getFieldName().equals(PASSWORD_NAME))
				{
					xPassword = xTemp;
				}
			}
			if (xPrivateKey == null || xPassword == null)
			{
				// param is not found in the request
				throw new KOAException(ErrorConstants.VALIDATE_PRIVATE_KEY);
			}
			g_sPassword = xPassword.getString();
			g_baPrivateKey = new byte[xPrivateKey.getInputStream().available()];
			xPrivateKey.getInputStream().read(g_baPrivateKey);
			// Check the private key on validity before going further 
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[prepareVoteCount.init] check the private key for validity");
			try
			{
				Convertor xConvertor = new Convertor();
				PrivateKey xTempPrivKey =
					xConvertor.byteArrayToPrivateKey(
						g_baPrivateKey,
						g_sPassword);
				if (xTempPrivKey == null)
				{
					// Log the error in private key saving for monitor by tivoli 
					String[] params = { "private" };
					KOALogHelper.logErrorCode(
						"prepareVoteCount.init",
						ErrorConstants.ERR_PARSE_PUB_PRIVKEY,
						params,
						null);
					KOALogHelper.logError(
						"prepareVoteCount.init",
						"problems parsing the private key",
						null);
					throw new KOAException(ErrorConstants.VALIDATE_PRIVATE_KEY);
				}
			}
			catch (KOAException koae)
			{
				// Log the error in private key saving for monitor by tivoli 
				String[] params = { "private" };
				KOALogHelper.logErrorCode(
					"prepareVoteCount.init",
					ErrorConstants.ERR_PARSE_PUB_PRIVKEY,
					params,
					koae);
				KOALogHelper.logError(
					"prepareVoteCount.init",
					"problems parsing the private key",
					koae);
				throw new KOAException(
					ErrorConstants.VALIDATE_PRIVATE_KEY,
					koae);
			}
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[prepareVoteCount.init] private Key file parsed, got private key..."
					+ g_baPrivateKey);
		}
		catch (java.io.IOException ioe)
		{
			String[] params = { "InputStream" };
			KOALogHelper.logErrorCode(
				"prepareVoteCount.init",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.COMMAND_COUNTVOTE_INIT, ioe);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"prepareVoteCount.init",
				"KOA Exception during initialize of the command",
				koae);
			throw koae;
		}
		catch (Exception e)
		{
			throw new KOAException(ErrorConstants.COMMAND_COUNTVOTE_INIT, e);
		}
	}
	/**
	 * Update the current session.
	 * 
	 * @param HttpSession	The session to be updated
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
}