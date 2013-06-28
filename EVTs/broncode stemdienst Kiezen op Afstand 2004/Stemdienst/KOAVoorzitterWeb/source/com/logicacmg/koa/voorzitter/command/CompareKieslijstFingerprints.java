/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.CompareKieslijstFingerprints.java
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
  *  0.1.8		15-05-2003	Mku			Compare of the fingerprints...
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.voorzitter.command;
import java.rmi.RemoteException;
import com.logica.eplatform.command.AbstractTargetableCommand;
import com.logica.eplatform.command.CommandException;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.dataobjects.KiesLijstFingerprintCompareResult;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kieslijst.beans.KiesLijst;
import com.logicacmg.koa.kieslijst.beans.KiesLijstHome;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
import com.logicacmg.koa.voorzitter.command.CommandConstants;
/**
 * CompareKieslijstFingerprints.
 * Use this command to get the compare the fingerprints
 * of the Kieslijst.
 * 
 * @author KuijerM
 * 
 */
public class CompareKieslijstFingerprints
	extends AbstractTargetableCommand
	implements HttpCommand
{
	private java.lang.String RESULT_JSP = "comparefingerprints_result.jsp";
	private java.lang.String g_sCurrentState;
	private KiesLijstFingerprintCompareResult g_xCompareResult = null;
	/**
	 * The execute method on the CompareKieslijstFingerprints command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of the Kieslijst can not be created.
	 */
	public void execute() throws CommandException, EPlatformException
	{
		LogHelper.log(
			LogHelper.INFO,
			"[CompareKieslijstFingerprints.execute] start");
		try
		{
			KiesLijstHome xHome = ObjectCache.getInstance().getKiesLijstHome();
			/* create remote instance from the home interface */
			KiesLijst xKiesLijst = xHome.create();
			/* get the current state */
			g_xCompareResult = xKiesLijst.compareKieslijstFingerprint();
		}
		catch (CreateException ce)
		{
			String[] params = { "KiesLijst" };
			KOALogHelper.logErrorCode(
				"CompareKieslijstFingerprints.execute",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(
				ErrorConstants.CMD_COMPARE_FINGERPRINTS_ERR,
				ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "KiesLijst" };
			KOALogHelper.logErrorCode(
				"CompareKieslijstFingerprints.execute",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(
				ErrorConstants.CMD_COMPARE_FINGERPRINTS_ERR,
				re);
		}
	}
	/**
	 * Return the JSP to display errors.
	 * 
	 * @return String The error JSP
	 */
	public String getErrorJSP()
	{
		return CommandConstants.DEFAULT_ERROR_JSP;
	}
	/**
	 * Return the JSP page to display the result.
	 *
	 * @return String The result JSP
	 */
	public String getResultJSP()
	{
		return RESULT_JSP;
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
		LogHelper.trace(LogHelper.TRACE, "[CompareKieslijstFingerprints] init");
	}
	/**
	 * Update the current session.
	 * 
	 * @param HttpSession	The session to be updated
	 */
	public void updateSession(javax.servlet.http.HttpSession session)
	{
	}
	/**
	 * Return the compare result which was retrieved in the execute() method.
	 *
	 * @return KiesLIjstFingerprintCompareResult	The result of comparing the kieslijst fingerprint
	 */
	public KiesLijstFingerprintCompareResult getCompareResult()
	{
		return g_xCompareResult;
	}
}
