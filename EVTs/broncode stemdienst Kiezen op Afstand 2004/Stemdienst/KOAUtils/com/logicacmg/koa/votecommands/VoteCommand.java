/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.votecommands.VoteCommand.java
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
  *  0.1		28-04-2003	XUi			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.votecommands;
import java.util.Hashtable;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logica.eplatform.command.CommandException;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.controller.client.ClientManager;
import com.logicacmg.koa.dataobjects.Kandidaat;
import com.logicacmg.koa.dataobjects.Stem;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kieslijst.beans.KiesLijst;
import com.logicacmg.koa.kieslijst.beans.KiesLijstHome;
import com.logicacmg.koa.soap.command.SOAPCommand;
import com.logicacmg.koa.soap.request.SOAPRequest;
import com.logicacmg.koa.stemproces.beans.StemprocesSessionEJB;
import com.logicacmg.koa.stemproces.beans.StemprocesSessionEJBHome;
import com.logicacmg.koa.utils.InputValidator;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
import com.logicacmg.koa.votecommands.CommandConstants;
/**
 * Command to issue the vote
 *
 * @author GroenevA
 */
public class VoteCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand, SOAPCommand
{
	private final static String NEXT_JSP = "/WEB-INF/jsp/transactioncode.jsp";
	private final static String PREVIOUS_JSP =
		"/WEB-INF/jsp/ChooseCandidate.jsp";
	private String g_sResultJSP = CommandConstants.DEFAULT_ERROR_JSP;
	private String sErrorMessage = null;
	private String sVoterID = null;
	private String sPassword = null;
	private String sKandidaatcode = null;
	private String sModaliteit = null;
	private StemTransactie xStemTransactie = null;
	private String sNavigation = null;
	private boolean bUpdateVoteCounter = false;
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
		if (sNavigation != null
			&& sNavigation.equals(CommandConstants.NAVIGATION_PREVIOUS))
		{
			g_sResultJSP = PREVIOUS_JSP;
		}
		if (xStemTransactie != null
			&& xStemTransactie.VoteStatus == StemTransactie.OK)
		{
			g_sResultJSP = NEXT_JSP;
		}
		return g_sResultJSP;
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
		HttpSession xSession = request.getSession(true);
		sVoterID = (String) xSession.getAttribute(CommandConstants.STEMCODE);
		sPassword = (String) xSession.getAttribute(CommandConstants.PASSWORD);
		sKandidaatcode =
			(String) xSession.getAttribute(CommandConstants.KANDIDAATCODE);
		sModaliteit = ComponentType.WEB;
		sNavigation = request.getParameter(CommandConstants.NAVIGATION_FIELD);
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VoteCommand] sNavigation = " + sNavigation);
	}
	/**
	 * Update the current session.
	 * 
	 * @param HttpSession	The session to be updated
	 */
	public void updateSession(HttpSession session) throws EPlatformException
	{
	}
	/**
	 * Initialises the command. Here the parameters are
	 * extracted from the request.
	 *
	 * @param SOAPRequest			Object that encapsulates the request from the SOAP interface
	 * 
	 * @throws EPlatformException	necessary to fullfill abstract method signature
	 */
	public void init(SOAPRequest request) throws EPlatformException
	{
		sVoterID = (String) request.getParameter(CommandConstants.STEMCODE);
		sPassword = (String) request.getParameter(CommandConstants.PASSWORD);
		sKandidaatcode =
			(String) request.getParameter(CommandConstants.KANDIDAATCODE);
		sModaliteit = ComponentType.TEL;
	}
	/**
	 * The execute method on the Vote command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of EJB's can not be created.
	 */
	public void execute() throws CommandException, EPlatformException
	{
		if (sNavigation != null
			&& !sNavigation.equals(CommandConstants.VOTE_INDICATION))
		{
			return;
		}
		/* Check the candidate code and stemcode/wachtwoord for valid values */
		if (!InputValidator.validateCandidate(sKandidaatcode)
			|| !InputValidator.validateUser(sVoterID, sPassword))
		{
			g_sResultJSP = PREVIOUS_JSP;
			return;
		}
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[VoteCommand] get candidate.");
			// get the kandidaat
			KiesLijstHome xKiesLijstHome =
				ObjectCache.getInstance().getKiesLijstHome();
			KiesLijst xKLSession = xKiesLijstHome.create();
			Kandidaat xKandidaat = xKLSession.getKandidaat(sKandidaatcode);
			// create the stem, set kandidaat & modaliteit
			Stem xStem = new Stem();
			xStem.kandidaat = xKandidaat;
			xStem.modaliteit = sModaliteit;
			// call stemproces and issue vote
			StemprocesSessionEJBHome xStemprocesSessionEJBHome =
				ObjectCache.getInstance().getStemprocesSessionHome();
			StemprocesSessionEJB xStemproces =
				xStemprocesSessionEJBHome.create();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[VoteCommand] issue vote :-)");
			xStemTransactie = xStemproces.vote(xStem, sVoterID, sPassword);
			if (xStemTransactie.VoteStatus == StemTransactie.OK
				&& xStemTransactie.Modaliteit.equals(ComponentType.WEB))
			{
				bUpdateVoteCounter = true;
			}
		}
		catch (KOAException koae)
		{
			/* block system when voting failed */
			this.blockSystem();
			/* set transaction result for the TSM */
			xStemTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
			throw koae;
		}
		catch (java.rmi.RemoteException re)
		{
			/* block system when voting failed */
			this.blockSystem();
			/* set transaction result for the TSM */
			xStemTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
			String[] params = { "StemprocesSessionBean" };
			KOALogHelper.logErrorCode(
				"[VoteCommand]",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.VOTER_EXECUTE_VOTE_ERROR);
		}
		catch (javax.ejb.CreateException ce)
		{
			/* block system when voting failed */
			this.blockSystem();
			/* set transaction result for the TSM */
			xStemTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
			String[] params = { "StemprocesSessionBean" };
			KOALogHelper.logErrorCode(
				"[VoteCommand]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.VOTER_EXECUTE_VOTE_ERROR);
		}
		catch (Throwable e)
		{
			/* block system when voting failed */
			this.blockSystem();
			/* set transaction result for the TSM */
			xStemTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
			throw new KOAException(ErrorConstants.VOTER_EXECUTE_VOTE_ERROR);
		}
		if (xStemTransactie.VoteStatus != StemTransactie.OK)
		{
			switch (xStemTransactie.VoteStatus)
			{
				case StemTransactie.ACCOUNT_LOCKED :
					throw new KOAException(ErrorConstants.ERR_NO_AUTORISATION);
				case StemTransactie.ALREADY_VOTED :
					throw new KOAException(ErrorConstants.ERR_ALREADY_VOTED);
				case StemTransactie.ELECTION_NOT_YET_OPEN :
					throw new KOAException(
						ErrorConstants.ERR_ELECTION_NOT_YET_OPEN);
				case StemTransactie.ELECTION_CLOSED :
					throw new KOAException(ErrorConstants.ERR_ELECTION_CLOSED);
				case StemTransactie.INVALID_CREDENTIALS :
					throw new KOAException(
						ErrorConstants.ERR_INVALID_CREDENTIALS);
				case StemTransactie.ELECTION_SUSPENDED :
					throw new KOAException(
						ErrorConstants.ERR_ELECTION_SUSPENDED);
				case StemTransactie.ELECTION_BLOCKED :
					throw new KOAException(ErrorConstants.ERR_ELECTION_BLOCKED);
				case StemTransactie.KIEZER_DELETED :
					throw new KOAException(
						ErrorConstants.ERR_INVALID_CREDENTIALS);
			}
		}
	}
	/**
	 * Update the vote counter after execution (if bUpdateVoteCounter is set to true).
	 * 
	 * @throws EPlatformException	thrown to fullfill abstract method signature
	 */
	public void postExecution() throws EPlatformException
	{
		/* locally add one to the counter if it should be updated*/
		if (bUpdateVoteCounter)
		{
			ClientManager.updateCounter(
				ComponentType.WEB,
				CounterKeys.STEMMEN_UITGEBRACHT);
		}
	}
	/**
	 * Returns the stemtransactie, which is retrieved in the execute() method
	 * 
	 * @return StemTransactie  An object which contains data regarding the vote transaction
	 */
	public StemTransactie getStemTransactie()
	{
		return xStemTransactie;
	}
	/**
	 * Block system when voting failed
	 */
	private void blockSystem()
	{
		/* block system when voting failed */
		KOALogHelper.logError(
			"VoteCommand.blockSystem",
			"Could not update the vote, blocking system...",
			null);
		try
		{
			Hashtable htProps = new Hashtable();
			htProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(
					JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
			htProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
			/* create the initial context */
			InitialContext jndiContext = new InitialContext(htProps);
			/* look up the home interface */
			Object obj =
				jndiContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			ControllerHome home =
				(ControllerHome) PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			Controller controller = home.create();
			/* block the system */
			controller.block();
			KOALogHelper.logError(
				"VoteCommand.blockSystem",
				"System blocked...",
				null);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[VoteCommand.blockSystem]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[VoteCommand.blockSystem]",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
		}
		catch (javax.ejb.CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[VoteCommand.blockSystem]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"VoteCommand.blockSystem",
				"KOAException during block of system, system not blocked",
				koae);
		}
	}
}