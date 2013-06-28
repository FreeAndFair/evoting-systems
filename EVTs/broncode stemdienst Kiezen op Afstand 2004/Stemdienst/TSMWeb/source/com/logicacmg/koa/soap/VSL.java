/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.VSL.java
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
package com.logicacmg.koa.soap;
import java.rmi.RemoteException;

import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.ticket.Ticket;
import com.logica.eplatform.ticket.TicketRequest;
import com.logica.eplatform.util.SystemProperties;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.controller.beans.Koa_state;
import com.logicacmg.koa.controller.client.ClientManager;
import com.logicacmg.koa.dataobjects.KandidaatResponse;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.soap.command.SOAPCommand;
import com.logicacmg.koa.soap.request.SOAPRequest;
import com.logicacmg.koa.soap.response.AreYouThereResponse;
import com.logicacmg.koa.soap.response.SubscribeResponse;
import com.logicacmg.koa.soap.response.UnsubscribeResponse;
import com.logicacmg.koa.soap.response.VerifyCandidateResponse;
import com.logicacmg.koa.soap.response.VerifyVoterResponse;
import com.logicacmg.koa.soap.response.VoteResponse;
import com.logicacmg.koa.soap.response.VotingDetails;
import com.logicacmg.koa.ticket.KOATicketFactory;
import com.logicacmg.koa.ticket.KOATicketResponse;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
import com.logicacmg.koa.votecommands.VerifyCandidateCommand;
import com.logicacmg.koa.votecommands.VoteCommand;
public class VSL
{
	/**
	 * Verify a voter with the KR
	 * 
	 * @param sender 	Id of the sending TSM
	 * @param sessionID	Technical session Id which the voter has with the TSM
	 * @param voterID 	The voterid of the voter (stemcode)
	 * @param password 	The password entered by the voter in clear text
	 * 
	 * @return VerifyVoterResponse Response object containing the status code for the verification
	 * 
	 */
	public VerifyVoterResponse verifyVoter(
		String sender,
		String sessionID,
		String voterID,
		String password)
	{
		/*
		 *	Retrieve a stemtransactie object which indicates the status of the voter.
		 */
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: "
				+ getTSMIP()
				+ " issued verifyVoter for stemcode: "
				+ voterID
				+ "(session-id: "
				+ sessionID
				+ ")");
		VerifyVoterResponse vvResponse = new VerifyVoterResponse();
		StemTransactie xStemTransactie = null;
		vvResponse.setReturncode(-2);
		// check if the input parameters != null
		if (sender == null
			|| sender.trim().length() == 0
			|| sessionID == null
			|| sessionID.trim().length() == 0
			|| voterID == null
			|| voterID.trim().length() == 0
			|| password == null
			|| password.trim().length() == 0)
		{
			// invalid import parameters 
			if (voterID == null
				|| voterID.trim().length() == 0
				|| password == null
				|| password.trim().length() == 0)
			{
				vvResponse.setReturncode(1);
			}
		}
		else
		{
			try
			{
				KOATicketResponse xTicketResponse =
					getTicketResponse(voterID, password, true);
				xStemTransactie = xTicketResponse.getStemTransactie();
				if (xStemTransactie != null)
				{
					if (xStemTransactie.VoteStatus == xStemTransactie.OK)
					{
						/* Here we should return the ballot id */
						vvResponse.setReturncode(0);
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.ELECTION_NOT_YET_OPEN
							|| xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_CLOSED)
					{
						vvResponse.setReturncode(-1);
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.ELECTION_BLOCKED)
					{
						vvResponse.setReturncode(-1);
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.ELECTION_SUSPENDED)
					{
						vvResponse.setReturncode(-1);
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.INVALID_CREDENTIALS)
					{
						vvResponse.setReturncode(1);
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.KIEZER_DELETED)
					{
						vvResponse.setReturncode(1);
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.ACCOUNT_LOCKED)
					{
						vvResponse.setReturncode(2);
						/* We need to find the time to unlock */
						vvResponse.setTimeToUnlock(
							xTicketResponse.getTimeToUnlock());
					}
					else if (
						xStemTransactie.VoteStatus
							== xStemTransactie.ALREADY_VOTED)
					{
						vvResponse.setReturncode(3);
						// Because the voter has already voted, 
						// fill in the votingdetails
						VotingDetails vDetails = new VotingDetails();
						vDetails.setTX_code(
							xStemTransactie.Transactienummer.toString());
						vDetails.setTimestamp_voted(xStemTransactie.VotingTime);
						vDetails.setChannel(
							ComponentType.getModaliteitAsInt(
								xStemTransactie.Modaliteit));
						vvResponse.setVotingDetails(vDetails);
					}
				}
			}
			catch (KOAException koae)
			{
				vvResponse.setReturncode(-2);
				KOALogHelper.logError("VSL.verifyVoter", "KOAException", koae);
				koae.printStackTrace();
			}
		}
		return vvResponse;
	}
	/**
	 * Verify the candidate a voter wants to vote for.
	 * 
	 * @param sender 		Id of the sending TSM
	 * @param sessionID		Technical session Id which the voter has with the TSM
	 * @param voterID 		The voterid of the voter (stemcode)
	 * @param password 		The password entered by the voter in clear text
	 * @param candidateID 	The candidate the voter wants to vote for (kandidaatcode)
	 *
	 * @return VerifyCandidateResponse Response object containing the status code for the verification
	 */
	public VerifyCandidateResponse verifyCandidate(
		String sender,
		String sessionID,
		String voterID,
		String password,
		String candidateID)
	{
		/* 
		 * Here we want to use the same command the web-user does 
		 * which is the VerifyCandidateCommand
		 */
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: "
				+ getTSMIP()
				+ " issued verifyCandidate for stemcode: "
				+ voterID
				+ "(session-id: "
				+ sessionID
				+ ")");
		VerifyCandidateResponse vcResponse = new VerifyCandidateResponse();
		vcResponse.setReturncode(-2);
		// check if the input parameters != null
		if (sender == null
			|| sender.trim().length() == 0
			|| sessionID == null
			|| sessionID.trim().length() == 0
			|| voterID == null
			|| voterID.trim().length() == 0
			|| password == null
			|| password.trim().length() == 0
			|| candidateID == null
			|| candidateID.trim().length() == 0)
		{
			// invalid import parameters 
		}
		else
		{
			try
			{
				// check the system state with the clientmanager
				if (!ClientManager.getState().equals(SystemState.OPEN))
				{
					// if the election is not open, set the response to -1
					vcResponse.setReturncode(-1);
				}
				else
				{
					// the election is open, go on and verify the candidate
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[VSL.verifyCandidate] Requesting ticket");
					KOATicketResponse xTicketResponse =
						getTicketResponse(voterID, password, false);
					if (xTicketResponse.getTicket() != null)
					{
						VerifyCandidateCommand command =
							new VerifyCandidateCommand();
						SOAPRequest xsRequest = new SOAPRequest();
						xsRequest.setParameter("KANDIDAATCODE", candidateID);
						xsRequest.setParameter("STEMCODE", voterID);
						command.init(xsRequest);
						command =
							(VerifyCandidateCommand) executeCommand(command,
								xTicketResponse.getTicket());
						// if kandidaatresponse = ok, set response status to 0
						KandidaatResponse xKandidaatResponse =
							command.getKandidaatResponse();
						if (xKandidaatResponse == null)
						{
							KOALogHelper.log(
								KOALogHelper.TRACE,
								"[VSL.verifyCandidate] Kandidaatresponse is null.");
						}
						else if (
							xKandidaatResponse.status
								== KandidaatResponse.KANDIDATE_OK)
						{
							vcResponse.setReturncode(0);
						}
						else if (
							xKandidaatResponse.status
								== KandidaatResponse.KANDIDATE_NOT_FOUND
								|| xKandidaatResponse.status
									== KandidaatResponse.KANDIDATE_NOT_NUMERIC
								|| xKandidaatResponse.status
									== KandidaatResponse
										.KANDIDATE_NOT_CORRECT_LENGTH)
						{
							vcResponse.setReturncode(1);
						}
					}
					else
					{
						/* 
						 * dont check for credentials. if ticket is null, return 0 (candidate OK) 
						 */
						vcResponse.setReturncode(0);
					}
				}
			}
			catch (EPlatformException ee)
			{
				vcResponse.setReturncode(-2);
				KOALogHelper.logError(
					"VSL.verifyCandidate",
					"KOAException",
					ee);
			}
		}
		return vcResponse;
	}
	/**
	 * Issue a vote via the SOAP interface
	 * 
	 * @param sender 		The id of the sending IVR.
	 * @param sessionID 	The sessionID for the caller who is connected to the IVR.
	 * @param voterID 		The id of the voter (stemcode).
	 * @param password 		The password of the voter (clear text).
	 * @param candidateID 	The ID of the candidate the voter wants to vote for.
	 * 
	 * @return VoteReponse A response object which contains a returncode indicating whether the vote was succesful.
	 */
	public VoteResponse vote(
		String sender,
		String sessionID,
		String voterID,
		String password,
		String candidateID)
	{
		// The actual voting routine
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: "
				+ getTSMIP()
				+ " issued vote for stemcode: "
				+ voterID
				+ "(session-id: "
				+ sessionID
				+ ")");
		VoteResponse vResponse = new VoteResponse();
		StemTransactie xStemTransactie = null;
		vResponse.setReturncode(-2);
		// check if the input parameters != null
		if (sender == null
			|| sender.trim().length() == 0
			|| sessionID == null
			|| sessionID.trim().length() == 0
			|| voterID == null
			|| voterID.trim().length() == 0
			|| password == null
			|| password.trim().length() == 0
			|| candidateID == null
			|| candidateID.trim().length() == 0)
		{
			// invalid import parameters 
		}
		else
		{
			try
			{
				KOATicketResponse xTicketResponse =
					getTicketResponse(voterID, password, false);
				xStemTransactie = xTicketResponse.getStemTransactie();
				if (xStemTransactie != null)
				{
					if (xStemTransactie.VoteStatus != xStemTransactie.OK)
					{
						// voter is not allowed to vote, find out why and set the returncode
						if (xStemTransactie.VoteStatus
							== xStemTransactie.ELECTION_NOT_YET_OPEN
							|| xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_CLOSED)
						{
							vResponse.setReturncode(-1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_BLOCKED)
						{
							vResponse.setReturncode(-1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_SUSPENDED)
						{
							vResponse.setReturncode(-1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.INVALID_CREDENTIALS)
						{
							vResponse.setReturncode(1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.KIEZER_DELETED)
						{
							vResponse.setReturncode(1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ACCOUNT_LOCKED)
						{
							vResponse.setReturncode(2);
							/* We need to find the time to unlock */
							vResponse.setTimeToUnlock(
								xTicketResponse.getTimeToUnlock());
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ALREADY_VOTED)
						{
							vResponse.setReturncode(3);
							/* Return a Votingdetails object */
							VotingDetails vDetails = new VotingDetails();
							vDetails.setTX_code(
								xStemTransactie.Transactienummer.toString());
							vDetails.setChannel(
								ComponentType.getModaliteitAsInt(
									xStemTransactie.Modaliteit));
							vDetails.setTimestamp_voted(
								xStemTransactie.VotingTime);
							vResponse.setVotingDetails(vDetails);
						}
					}
					else
					{
						// voter is allowed to vote, so start voting
						VoteCommand command = new VoteCommand();
						SOAPRequest xsRequest = new SOAPRequest();
						xsRequest.setParameter("KANDIDAATCODE", candidateID);
						xsRequest.setParameter("STEMCODE", voterID);
						xsRequest.setParameter("PASSWORD", password);
						command.init(xsRequest);
						command =
							(VoteCommand) executeCommand(command,
								xTicketResponse.getTicket());
						// NOW PROCESS THE RESULT OF THE VOTECOMMAND
						if (command == null)
						{
							KOALogHelper.log(
								KOALogHelper.TRACE,
								"Command is null!!");
						}
						xStemTransactie = command.getStemTransactie();
						if (xStemTransactie == null)
						{
							KOALogHelper.log(
								KOALogHelper.TRACE,
								"Stemtransactie is null!!");
						}
						// Determine the correct response code for the stemtransactie
						if (xStemTransactie.VoteStatus
							== xStemTransactie.ELECTION_NOT_YET_OPEN
							|| xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_CLOSED)
						{
							vResponse.setReturncode(-1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_BLOCKED)
						{
							vResponse.setReturncode(-1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ELECTION_SUSPENDED)
						{
							vResponse.setReturncode(-1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.INVALID_CREDENTIALS)
						{
							vResponse.setReturncode(1);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ACCOUNT_LOCKED)
						{
							vResponse.setReturncode(2);
							/* We need to find the time to unlock */
							vResponse.setTimeToUnlock(
								xTicketResponse.getTimeToUnlock());
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.ALREADY_VOTED)
						{
							vResponse.setReturncode(3);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.KIEZER_DELETED)
						{
							vResponse.setReturncode(2);
						}
						else if (
							xStemTransactie.VoteStatus
								== xStemTransactie.INVALID_CANDIDATE)
						{
							vResponse.setReturncode(4);
						}
						else if (
							xStemTransactie.VoteStatus == xStemTransactie.OK)
						{
							vResponse.setReturncode(0);
							VotingDetails vDetails = new VotingDetails();
							vDetails.setTX_code(
								xStemTransactie.Transactienummer.toString());
							vDetails.setChannel(
								ComponentType.getModaliteitAsInt(
									xStemTransactie.Modaliteit));
							vDetails.setTimestamp_voted(
								xStemTransactie.VotingTime);
							vResponse.setVotingDetails(vDetails);
						}
						/* check state before going on... */
						String sCurrentState = this.getCurrentState();
						if (sCurrentState.equals(SystemState.BLOCKED))
						{
							vResponse.setReturncode(-2);
						}
					}
					// stemtransactie appears to be null, so voting fails
				}
			}
			catch (EPlatformException epe)
			{
				vResponse.setReturncode(-2);
				KOALogHelper.logError("VSL.vote", "EPlatform exception", epe);
			}
		}
		return vResponse;
	}
	/**
	 * Method for the TSM to report a failure with the system.
	 * The errormessage will be written to the error log.
	 * 
	 * @param failureCode	failure code
	 * @param errormessage	Text describing the error
	 */
	public void reportFailure(int failureCode, String errormessage)
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: "
				+ getTSMIP()
				+ " issued reportFailure with failurecode: "
				+ failureCode);
		// Get the remote IP-address
		MessageContext msgContext = MessageContext.getCurrentContext();
		String sRemoteAddr = (String) msgContext.getProperty("remoteaddr");
		KOALogHelper.logError(
			"TSM " + sRemoteAddr + " ",
			failureCode + ": " + errormessage,
			null);
	}
	/**
	 * Method for the TSM to check whether the application is still alive
	 *  
	 * @return AreYouThereResponse Reponse object
	 * 
	 */
	public AreYouThereResponse areYouThere()
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: " + getTSMIP() + " issued areYouThere");
		int iReturncode = -2;
		/* check the current state with the controller */
		try
		{
			String sState = ClientManager.getState();
			if (!sState.equals(SystemState.OPEN))
			{
				iReturncode = -1;
			}
			else
			{
				iReturncode = 0;
			}
		}
		catch (KOAException koae)
		{
			iReturncode = -2;
			KOALogHelper.logError(
				"VSL.areYouThere",
				"Retrieve SystemState failed",
				koae);
		}
		AreYouThereResponse response = new AreYouThereResponse();
		response.setReturncode(iReturncode);
		return response;
	}
	/**
	 * Subscribes a TSM with the controller
	 * 
	 * @param sender ID of the subscribing TSM
	 * 
	 * @return SubscribeResponse Reponse object
	 */
	public SubscribeResponse subscribe(String sender)
	{
		int iState = -1;
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: "
				+ getTSMIP()
				+ " issued subscribe with sender ID: "
				+ sender);
		String sSender = sender;
		/* check the input parameters */
		if (sender == null || sender.trim().length() == 0)
		{
			// no input parameter
			iState = -1;
		}
		else
		{
			/* subscribe this TSM module  with the controller */
			try
			{
				ClientManager.subscribe(ComponentType.TEL, getTSMIP(), sSender);
				String sState = ClientManager.getState();
				iState = SystemState.getStateAsInt(sState);
			}
			catch (KOAException koae)
			{
				iState = -1;
				KOALogHelper.logError(
					"VSL.subscribe",
					"Cannot subscribe TSM module: "
						+ sSender
						+ " with IP: "
						+ getTSMIP(),
					koae);
			}
		}
		SubscribeResponse response = new SubscribeResponse();
		response.setStatus(iState);
		return response;
	}
	/**
	 * Unsubscribes a TSM with the controller
	 * 
	 * @param sender ID of the unsubscribing TSM
	 * 
	 * @return UnsubscribeResponse Reponse object
	 */
	public UnsubscribeResponse unsubscribe(String sender)
	{
		int iReturncode = 0;
		KOALogHelper.log(
			KOALogHelper.INFO,
			"TSM with IP: "
				+ getTSMIP()
				+ " issued unsubscribe with sender ID: "
				+ sender);
		String sSender = sender;
		/* check the input parameters */
		if (sender == null || sender.trim().length() == 0)
		{
			// no input parameter
			iReturncode = -1;
		}
		else
		{
			/* unsubscribe this TSM module  with the controller */
			try
			{
				ClientManager.unsubscribe(
					ComponentType.TEL,
					getTSMIP(),
					sSender);
			}
			catch (KOAException koae)
			{
				iReturncode = -1;
				KOALogHelper.logError(
					"VSL.unsubscribe",
					"Cannot unsubscribe TSM module: "
						+ sSender
						+ " with IP: "
						+ getTSMIP(),
					koae);
			}
		}
		UnsubscribeResponse uResponse = new UnsubscribeResponse();
		uResponse.setReturncode(iReturncode);
		return uResponse;
	}
	/**
	 * Executes a SOAPCommand the way the generic ePlatform servlet
	 * would do.
	 * 
	 * @param command	The command to execute.
	 * @param ticket	The ticket containing the users credentials
	 * 
	 * @return SOAPCommand the command with the result objects set
	 */
	private SOAPCommand executeCommand(SOAPCommand command, Ticket ticket)
	{
		try
		{
			/* set command target */
			command.setCommandTarget(getCommandTarget());
			/* pre execute command */
			command.preExecution();
			/* execute command */
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[VSL] Starting performExecute on Command: "
					+ command
					+ " for user: "
					+ ticket.getUserID());
			command = (SOAPCommand) command.performExecute(ticket);
			/* post execute command */
			command.postExecution();
			return command;
		}
		catch (Exception e)
		{
			/* display errormessages made by the ErrorMessageFactory */
			String[] params = { "Could not execute command for SOAP request" };
			KOALogHelper.logErrorCode(
				"VSL.executeCommand",
				ErrorConstants.ERR_COMM_TSM_TO_VSL,
				params,
				e);
			return null;
		}
	}
	/**
	 * Get the commandtarget to execute the commands in.
	 * 
	 * @return EJBCommandTarget the commandtarget
	 */
	private EJBCommandTarget getCommandTarget()
	{
		//Perform the lookup
		EJBCommandTarget commandTarget = null;
		EJBCommandTargetHome targetHome = null;
		KOALogHelper.log(KOALogHelper.TRACE, "[VSL] initCommandTarget");
		SystemProperties props =
			com.logica.eplatform.util.SystemProperties.getSystemProperties();
		targetHome = ObjectCache.getInstance().getTSMTargetHome();
		try
		{
			commandTarget = targetHome.create();
		}
		catch (CreateException ce)
		{
			String[] params = { "EJBCommandTarget" };
			KOALogHelper.logErrorCode(
				"VSL.getCommandTarget",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
		}
		catch (RemoteException re)
		{
			String[] params = { "EJBCommandTarget" };
			KOALogHelper.logErrorCode(
				"VSL.getCommandTarget",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
		}
		catch (Exception e)
		{
			String[] params = { "EJBCommandTarget" };
			KOALogHelper.logErrorCode(
				"VSL.getCommandTarget",
				ErrorConstants.ERR_CREATE,
				params,
				e);
		}
		return commandTarget;
	}
	/**
	 * Get a ticket for the user
	 * 
	 * @param voterID		The username.
	 * @param password		The password.
	 * @param addLoginCount A boolean indicating if this request should be added to the voter's logincount
	 * 
	 * @return KOATicketResponse A Ticket which will only be returned if the elections are open and the user credentials are valid.
	 */
	private KOATicketResponse getTicketResponse(
		String voterID,
		String password,
		boolean addLoginCount)
		throws KOAException
	{
		com.logica.eplatform.ticket.TicketRequest xRequest =
			new com.logica.eplatform.ticket.TicketRequest();
		KOATicketResponse xTicketResponse = null;
		xRequest.setCredential(TicketRequest.KEY_USERNAME, voterID);
		xRequest.setCredential(TicketRequest.KEY_PASSWORD, password);
		KOATicketFactory xFactory =
			(KOATicketFactory) KOATicketFactory.getTicketFactory();
		try
		{
			xTicketResponse =
				xFactory.getTicketResponse(
					xRequest,
					ComponentType.TEL,
					addLoginCount);
		}
		catch (com.logica.eplatform.error.EPlatformException epe)
		{
			KOALogHelper.logError(
				"VSL.getTicket",
				"Error getting ticketresponse",
				null);
		}
		return xTicketResponse;
	}
	/**
	 * Get the IP address of the TSM
	 * 
	 * @return String the string containing the ip address of the tsm
	 */
	private String getTSMIP()
	{
		MessageContext msgContext = MessageContext.getCurrentContext();
		return (String) msgContext.getProperty("remoteaddr");
	}
	/**
	 * Get the current state of the system
	 * 
	 * @return String the string containing the current state
	 */
	private String getCurrentState()
	{
		KOALogHelper.log(KOALogHelper.TRACE, "[VSL] getCurrentState");
		String sReturnState = SystemState.UNKNOWN;
		try
		{
			Koa_state state = ObjectCache.getInstance().getState();
			sReturnState = state.getCurrent_state();
		}
		catch (RemoteException re)
		{
			String[] params = { "koa state" };
			KOALogHelper.logErrorCode(
				"VSL.getCurrentState",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
		}
		catch (Exception e)
		{
			String[] params = { "koa state" };
			KOALogHelper.logErrorCode(
				"VSL.getCurrentState",
				ErrorConstants.ERR_CREATE,
				params,
				e);
		}
		return sReturnState;
	}
}