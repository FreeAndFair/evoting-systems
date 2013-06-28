/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.ticket.KOATicketFactory.java
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
  *  0.1		07-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.ticket;
import java.io.IOException;
import java.rmi.RemoteException;
import java.util.Date;
import java.util.Hashtable;
import java.util.Vector;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logica.eplatform.error.ErrorMessageFactory;
import com.logica.eplatform.ticket.Ticket;
import com.logica.eplatform.ticket.TicketFactory;
import com.logica.eplatform.ticket.TicketRequest;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.dataobjects.Kiezer;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kr.beans.KRSessionEJB;
import com.logicacmg.koa.kr.beans.KRSessionEJBHome;
import com.logicacmg.koa.ticket.KOATicket;
import com.logicacmg.koa.ticket.KOATicketResponse;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The factory to create tickets.
 * 
 * @author: KuijerM
 */
public class KOATicketFactory
	implements com.logica.eplatform.ticket.TicketFactory
{
	/* home interface for the kiezers bean */
	private KRSessionEJBHome g_xKRHome = null;
	/* Singleton implementation */
	static KOATicketFactory instance = null;
	/**
	 * Private constructor
	 */
	private KOATicketFactory()
	{
		Hashtable htProps = new Hashtable();
		try
		{
			/* setup the parameters for the initial context */
			htProps.put(
				Context.INITIAL_CONTEXT_FACTORY,
				JNDIProperties.getProperty(JNDIProperties.KR_CONTEXT_FACTORY));
			htProps.put(
				Context.PROVIDER_URL,
				JNDIProperties.getProperty(JNDIProperties.KR_PROVIDER));
			/* create the initial context */
			InitialContext icContext = new InitialContext(htProps);
			/* get the bean home interface */
			Object obj =
				icContext.lookup(
					JNDIProperties.getProperty(JNDIProperties.KR_SESSION_EJB));
			g_xKRHome =
				(KRSessionEJBHome) PortableRemoteObject.narrow(
					obj,
					KRSessionEJBHome.class);
		}
		catch (NamingException ne)
		{
			String[] params = { "KRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KOATicketFActory",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logErrorCode(
				"KOATicketFActory",
				koae.getErrorCode(),
				koae.getParameters(),
				koae);
		}
	}
	/**
	 * Gets the ticket response for the ticketrequest, containing a ticket if provided
	 * and information about the result of the ticket request.
	 * 
	 * @param request 		The ticketrequest that is issued
	 * @param sModality		The modality (web or phone)
	 * @param addLoginCount boolean indicating if the counter for the login count should be updated
	 * 
	 * @return KOATicketResponse response containing the ticket and response information
	 * 
	 * @throws KOAException if something goes wrong during the get of the ticket response
	 */
	public KOATicketResponse getTicketResponse(
		TicketRequest request,
		String sModality,
		boolean addLoginCount)
		throws KOAException
	{
		KOATicketResponse xTicketResponse = new KOATicketResponse();
		Vector roles = new Vector();
		/* get the errormessage factory instance */
		ErrorMessageFactory msgFactory = null;
		try
		{
			msgFactory = ErrorMessageFactory.getErrorMessageFactory();
		}
		catch (IOException ioe)
		{
			KOALogHelper.logError(
				"KOATicketFactory.getTicketResponse",
				"Failed to get status messages from ErrorMessageFactory",
				ioe);
		}
		/* exit if no message factory is present */
		if (msgFactory == null)
			throw new KOAException();
		/* reset the message */
		String sMessage = "";
		StemTransactie xStemTransactie = null;
		/* get the username and password from the ticket request */
		String sStemcode =
			(String) request.getCredential(TicketRequest.KEY_USERNAME);
		String sWachtwoord =
			(String) request.getCredential(TicketRequest.KEY_PASSWORD);
		KRSessionEJB xKR = null;
		try
		{
			/* get the remote interface */
			xKR = g_xKRHome.create();
			/* check if the person is authorized to vote */
			xStemTransactie =
				xKR.verifyKiezer(
					sStemcode,
					sWachtwoord,
					sModality,
					addLoginCount);
			if (xStemTransactie == null)
			{
				KOALogHelper.logError(
					"KOATicketFActory.getTicket",
					"Cannot retrieve result of verify kiezer",
					null);
				sMessage =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_KIEZER_ERR,
						null);
				xStemTransactie = new StemTransactie();
				xStemTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
				/* dont provide a ticket if the username or password is null */
				xTicketResponse.setStemTransactie(xStemTransactie);
				/* dont provide a ticket if the username or password is null */
				xTicketResponse.setMessage(sMessage);
				return xTicketResponse;
			}
			else if (
				xStemTransactie.VoteStatus == StemTransactie.VOTING_FAILED)
			{
				KOALogHelper.logError(
					"KOATicketFActory.getTicket",
					"Cannot retrieve result of verifiy kiezer, voting failed",
					null);
				sMessage =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_KIEZER_ERR,
						null);
				xTicketResponse.setStemTransactie(xStemTransactie);
				/* dont provide a ticket if the username or password is null */
				xTicketResponse.setMessage(sMessage);
				return xTicketResponse;
			}
		}
		catch (RemoteException re)
		{
			String[] params = { "KRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KOATicketFActory.getTicket",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOAException();
		}
		catch (CreateException ce)
		{
			String[] params = { "KRSessionEJB" };
			KOALogHelper.logErrorCode(
				"KOATicketFActory.getTicket",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOAException();
		}
		/* check the stemtransactie */
		if (xStemTransactie.VoteStatus == StemTransactie.NON_NUMERIC_CODE)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] The stemcode does not consist of only digits.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.VERIFY_STEM_CODE_NUMERIC_ERR,
					null);
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.NINE_DIGITS)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] The stemcode is not 9 digits long.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.VERIFY_STEM_CODE_ERR,
					null);
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.ALREADY_VOTED)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] The voter has already voted.");
			roles.add(KOATicket.STEMGERECHTIGDE_ROLE);
			KOATicket ticket =
				new KOATicket(
					sStemcode,
					roles,
					new Date(
						System.currentTimeMillis()
							+ com
								.logica
								.eplatform
								.ticket
								.TicketConstants
								.TICKET_EXPIRY_TIME));
			/* set the ticket if the user has already voted */
			xTicketResponse.setTicket(ticket);
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_ALREADY_VOTED,
					null);
		}
		else if (
			xStemTransactie.VoteStatus == StemTransactie.INVALID_CREDENTIALS)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] The voter is not qualified.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_INVALID_CREDENTIALS,
					null);
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.ACCOUNT_LOCKED)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] The voter is not qualified, account has been locked.");
			Kiezer xKiezer = null;
			try
			{
				xKiezer = xKR.getKiezer(sStemcode);
				// get the timestamp unlock			
				long now = System.currentTimeMillis() / 1000;
				long unlock = xKiezer.timestampUnlock.getTime() / 1000;
				int iMinutes = (int) (unlock - now) / 60;
				if (iMinutes < 1)
				{
					iMinutes = 1;
				}
				xTicketResponse.setTimeToUnlock(iMinutes);
				String[] params =
					new String[] {
						FunctionalProps.getProperty(
							FunctionalProps.LOGIN_NR_TIMES_LOGIN),
						Integer.toString(iMinutes)};
				sMessage =
					msgFactory.getErrorMessage(
						ErrorConstants.ERR_ACCOUNT_TIMELOCK,
						params);
			}
			catch (java.rmi.RemoteException re)
			{
				KOALogHelper.logError(
					"KOATicketFActory.getTicket",
					"Caught RemoteException, cannot find locked kiezer.",
					re);
				throw new KOAException();
			}
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.KIEZER_DELETED)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] The voter is not qualified, the voter is deleted.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_KIEZER_DELETED,
					null);
		}
		else if (
			xStemTransactie.VoteStatus == StemTransactie.ELECTION_NOT_YET_OPEN)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] Elections are not yet open.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_ELECTION_NOT_YET_OPEN,
					null);
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.ELECTION_CLOSED)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] Elections are closed.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_ELECTION_CLOSED,
					null);
		}
		else if (
			xStemTransactie.VoteStatus == StemTransactie.ELECTION_SUSPENDED)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] Elections are currently suspended.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_ELECTION_SUSPENDED,
					null);
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.ELECTION_BLOCKED)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] Not possible to vote due to technical reasons.");
			sMessage =
				msgFactory.getErrorMessage(
					ErrorConstants.ERR_ELECTION_BLOCKED,
					null);
		}
		else if (xStemTransactie.VoteStatus == StemTransactie.OK)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOATicketFactory] Kiezer is stemgerechtigd.");
			/* add the burger role to the roles */
			roles.add(KOATicket.STEMGERECHTIGDE_ROLE);
			/* return the ticket based on the credentials */
			xTicketResponse.setTicket(
				new KOATicket(
					sStemcode,
					roles,
					new Date(
						System.currentTimeMillis()
							+ com
								.logica
								.eplatform
								.ticket
								.TicketConstants
								.TICKET_EXPIRY_TIME)));
		}
		xTicketResponse.setMessage(sMessage);
		xTicketResponse.setStemTransactie(xStemTransactie);
		return xTicketResponse;
	}
	/**
	 * Get a ticket based on the ticket request
	 * @param request the ticket request containing the username and password
	 * 
	 * @return Ticket the ticket based on the credentials
	 * 
	 * @deprecated This method is not supported. Use getTicketResponse instead.
	 */
	public Ticket getTicket(TicketRequest request)
		throws com.logica.eplatform.error.EPlatformException
	{
		KOALogHelper.logError(
			"KOATicketFactory.getTicket",
			"getTicket() is not supported, use getTicketResponse() instead.",
			null);
		throw new com.logica.eplatform.error.EPlatformException();
	}
	/**
	 * Gets the singleton implementation of the ticket factory. Static method.
	 * 
	 * @return TicketFactory The singleton implementation of the ticketfactory
	 * 
	 */
	public static TicketFactory getTicketFactory()
	{
		if (instance == null)
		{
			/* if no instance is created yet, create the instance */
			instance = new KOATicketFactory();
		}
		/* return the implementation */
		return instance;
	}
}