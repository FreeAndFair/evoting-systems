/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.votecommands.VerifyCandidateCommand.java
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
import javax.naming.InitialContext;

import com.logica.eplatform.command.CommandException;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.error.ErrorMessageFactory;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.dataobjects.KandidaatResponse;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kieslijst.beans.KiesLijst;
import com.logicacmg.koa.kieslijst.beans.KiesLijstHome;
import com.logicacmg.koa.soap.command.SOAPCommand;
import com.logicacmg.koa.soap.request.SOAPRequest;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
import com.logicacmg.koa.votecommands.CommandConstants;
/**
 * Verifies whether the candidate entered by the voter is valid.
 */
public class VerifyCandidateCommand
	extends com.logica.eplatform.command.AbstractTargetableCommand
	implements com.logica.eplatform.command.http.HttpCommand, SOAPCommand
{
	private final static String NEXT_JSP = "/WEB-INF/jsp/commitcandidate.jsp";
	private final static String SELF_JSP = "/WEB-INF/jsp/ChooseCandidate.jsp";
	private String sVoterId = null;
	private String sCandidateId = null;
	private String sCandidateIdPart1 = null;
	private String sCandidateIdPart2 = null;
	private String sCandidateIdPart3 = null;
	private Integer iVerifyCandidateAttempts = null;
	private KandidaatResponse xResponse = null;
	private String sValidationMessage = null;
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
		String sResultJSP = CommandConstants.DEFAULT_ERROR_JSP;
		switch (xResponse.status)
		{
			case KandidaatResponse.KANDIDATE_OK :
				sResultJSP = NEXT_JSP;
				break;
			case KandidaatResponse.KANDIDATE_NOT_FOUND :
			case KandidaatResponse.KANDIDATE_NOT_NUMERIC :
			case KandidaatResponse.KANDIDATE_NOT_CORRECT_LENGTH :
				sResultJSP = SELF_JSP;
				break;
		}
		return sResultJSP;
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
		sCandidateIdPart1 =
			(String) request.getParameter(CommandConstants.KANDIDAATCODE1);
		if (sCandidateIdPart1 == null)
		{
			sCandidateIdPart1 = "";
		}
		sCandidateIdPart2 =
			(String) request.getParameter(CommandConstants.KANDIDAATCODE2);
		if (sCandidateIdPart2 == null)
		{
			sCandidateIdPart2 = "";
		}
		sCandidateIdPart3 =
			(String) request.getParameter(CommandConstants.KANDIDAATCODE3);
		if (sCandidateIdPart3 == null)
		{
			sCandidateIdPart3 = "";
		}
		// Concateneer de drie invoervelden tot een veld
		sCandidateId =
			sCandidateIdPart1 + sCandidateIdPart2 + sCandidateIdPart3;
		sVoterId = (String) xSession.getAttribute(CommandConstants.STEMCODE);
		iVerifyCandidateAttempts =
			(Integer) xSession.getAttribute(
				CommandConstants.VERIFY_CANDIDATE_ATTEMPTS);
		// If iVerifyCandidateAttempts is not present as an attribute,
		// we initialize it to 1. This must be the first time a
		// kiezer tries to verify a candidate
		if (iVerifyCandidateAttempts == null)
		{
			iVerifyCandidateAttempts = new Integer(1);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VerifyCandidateCommand] xVoterID = " + sVoterId);
	}
	/**
	 * Update the current session.
	 * 
	 * @param HttpSession	The session to be updated
	 */
	public void updateSession(HttpSession session) throws EPlatformException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VerifyCandidateCommand] entering updateSession");
		// Save the kandidaatcode
		session.setAttribute(CommandConstants.KANDIDAATCODE, sCandidateId);
		// Increase the verify candidate attempts
		int iAttemptsCounter = iVerifyCandidateAttempts.intValue();
		iAttemptsCounter++;
		iVerifyCandidateAttempts = new Integer(iAttemptsCounter);
		// Save the verify candidate attempts
		session.setAttribute(
			CommandConstants.VERIFY_CANDIDATE_ATTEMPTS,
			iVerifyCandidateAttempts);
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
		sCandidateId =
			(String) request.getParameter(CommandConstants.KANDIDAATCODE);
		sVoterId = (String) request.getParameter(CommandConstants.STEMCODE);
		iVerifyCandidateAttempts = new Integer(1);
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[VerifyCandidateCommand] xVoterID = " + sVoterId);
	}
	/**
	 * The execute method on the VerifyCandidate command.
	 * This method is executed in the ejb command target.
	 * 
	 * @throws CommandException		necessary to fullfill abstract method signature
	 * @throws EPlatformException	thrown when the remote instance of EJB's can not be created.
	 */
	public void execute() throws CommandException, EPlatformException
	{
		try
		{
			// We need a reference to the error message factory in case something goes wrong
			ErrorMessageFactory xErrorMessageFactory = null;
			// We need to check if a kiezer has exceeded the maximum number of times he/she
			// can verify a kandidaat.
			int iMaxVerifyCandidateAttempts =
				FunctionalProps.getIntProperty(
					FunctionalProps.VERIFY_CANDIDATE_ATTEMPTS_COUNT);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[VerifyCandidateCommand] create initial context.");
			InitialContext jndiContext = new InitialContext();
			KiesLijstHome xKieslijstHome =
				ObjectCache.getInstance().getKiesLijstHome();
			KiesLijst xKieslijst = xKieslijstHome.create();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[VerifyCandidateCommand] verify candidate.");
			// Check if it is a valid candidate
			xResponse = xKieslijst.verifyKandidaat(sCandidateId, sVoterId);
			switch (xResponse.status)
			{
				case KandidaatResponse.KANDIDATE_OK :
					// If the candidate was correct, we reset the attempts to verify a candidate
					// to 0.
					iVerifyCandidateAttempts = new Integer(0);
					sValidationMessage = null;
					break;
				case KandidaatResponse.KANDIDATE_ERR :
					// Check if the kiezer has exceeded the number of times he/she is
					// allowed to verify a candidate
					if (iVerifyCandidateAttempts.intValue()
						>= iMaxVerifyCandidateAttempts)
					{
						throw new KOAException(
							ErrorConstants.VERIFY_CANDIDATE_ATTEMPTS_EXCEEDED);
					}
					throw new com.logicacmg.koa.exception.KOAException(
						ErrorConstants.ERR_CANDIDATE_ERR);
				case KandidaatResponse.KANDIDATE_NOT_NUMERIC :
					// Check if the kiezer has exceeded the number of times he/she is
					// allowed to verify a candidate
					if (iVerifyCandidateAttempts.intValue()
						>= iMaxVerifyCandidateAttempts)
					{
						throw new KOAException(
							ErrorConstants.VERIFY_CANDIDATE_ATTEMPTS_EXCEEDED);
					}
					xErrorMessageFactory =
						ErrorMessageFactory.getErrorMessageFactory();
					sValidationMessage =
						xErrorMessageFactory.getErrorMessage(
							ErrorConstants.VERIFY_CANDIDATE_CODE_NUMERIC_ERR,
							null);
					break;
				case KandidaatResponse.KANDIDATE_NOT_CORRECT_LENGTH :
					// Check if the kiezer has exceeded the number of times he/she is
					// allowed to verify a candidate
					if (iVerifyCandidateAttempts.intValue()
						>= iMaxVerifyCandidateAttempts)
					{
						throw new KOAException(
							ErrorConstants.VERIFY_CANDIDATE_ATTEMPTS_EXCEEDED);
					}
					xErrorMessageFactory =
						ErrorMessageFactory.getErrorMessageFactory();
					sValidationMessage =
						xErrorMessageFactory.getErrorMessage(
							ErrorConstants.VERIFY_CANDIDATE_CODE_ERR,
							null);
					break;
				case KandidaatResponse.KANDIDATE_NOT_FOUND :
					// Check if the kiezer has exceeded the number of times he/she is
					// allowed to verify a candidate
					if (iVerifyCandidateAttempts.intValue()
						>= iMaxVerifyCandidateAttempts)
					{
						throw new KOAException(
							ErrorConstants.VERIFY_CANDIDATE_ATTEMPTS_EXCEEDED);
					}
					xErrorMessageFactory =
						ErrorMessageFactory.getErrorMessageFactory();
					sValidationMessage =
						xErrorMessageFactory.getErrorMessage(
							ErrorConstants.ERR_CANDIDATE_NOT_FOUND,
							null);
					break;
				case KandidaatResponse.ELECTION_NOT_YET_OPEN :
					throw new KOAException(
						ErrorConstants.ERR_ELECTION_NOT_YET_OPEN);
				case KandidaatResponse.ELECTION_CLOSED :
					throw new KOAException(ErrorConstants.ERR_ELECTION_CLOSED);
				case KandidaatResponse.ELECTION_BLOCKED :
					throw new KOAException(ErrorConstants.ERR_ELECTION_BLOCKED);
				case KandidaatResponse.ELECTION_SUSPENDED :
					throw new KOAException(
						ErrorConstants.ERR_ELECTION_SUSPENDED);
			}
		}
		catch (javax.naming.NamingException xNamingException)
		{
			String[] params = { "Kieslijst" };
			KOALogHelper.logErrorCode(
				"[VerifyCandidateCommand]",
				ErrorConstants.ERR_NAMING,
				params,
				xNamingException);
			throw new KOAException(
				ErrorConstants.VCCOMMAND_ERROR,
				xNamingException);
		}
		catch (javax.ejb.CreateException ce)
		{
			String[] params = { "Kieslijst" };
			KOALogHelper.logErrorCode(
				"[VerifyCandidateCommand]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException(ErrorConstants.VCCOMMAND_ERROR, ce);
		}
		catch (java.rmi.RemoteException re)
		{
			String[] params = { "Kieslijst" };
			KOALogHelper.logErrorCode(
				"[VerifyCandidateCommand]",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException(ErrorConstants.VCCOMMAND_ERROR, re);
		}
		catch (java.io.IOException xIOExc)
		{
			String[] params = { "ErrorMessageFactory" };
			KOALogHelper.logErrorCode(
				"[VerifyCandidateCommand]",
				ErrorConstants.ERR_IO,
				params,
				xIOExc);
			throw new KOAException(ErrorConstants.VCCOMMAND_ERROR, xIOExc);
		}
	}
	/**
	 * Return kandidaatresponse containing whether the selected candidate was valid.
	 * 
	 * @return KandidaatResponse
	 */
	public KandidaatResponse getKandidaatResponse()
	{
		return xResponse;
	}
	/**
	 * Return validation message
	 * 
	 * @return String	the validation message (used to show in UI)
	 */
	public String getValidationMessage()
	{
		return sValidationMessage;
	}
	/**
	 * Returns whether the current candidate (if any yet known)
	 * is a blank vote candidate. The lastname of the candidate
	 * is compared with the functional indicator blank_vote_indicator.
	 * 
	 * @return boolean whether the candidate is the blank candidate
	 */
	public boolean isBlankCandidate()
	{
		try
		{
			/* get indicator from functional props */
			String blankVoteIndicator =
				FunctionalProps.getProperty(
					FunctionalProps.BLANK_VOTE_INDICATOR);
			/* compare indicator with lastname of candidate (if any( */
			if (blankVoteIndicator != null
				&& xResponse != null
				&& xResponse.kandidaat != null
				&& blankVoteIndicator.equals(xResponse.kandidaat.achterNaam))
			{
				return true;
			}
		}
		catch (KOAException koae)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[VerifyCandidateCommand.isBlankCandidate] Blank candidate indicator not found, return false");
		}
		return false;
	}
}