/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.stemproces.beans.StemprocesSessionEJBBean.java
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
  *  0.1		17-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.stemproces.beans;
import java.math.BigDecimal;
import java.sql.Timestamp;
import java.util.Date;

import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.constants.VoteConstants;
import com.logicacmg.koa.dataobjects.EncryptedStem;
import com.logicacmg.koa.dataobjects.Kandidaat;
import com.logicacmg.koa.dataobjects.Stem;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.esb.beans.ESBSessionEJB;
import com.logicacmg.koa.esb.beans.ESBSessionEJBHome;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kieslijst.beans.KiesLijst;
import com.logicacmg.koa.kieslijst.beans.KiesLijstHome;
import com.logicacmg.koa.kr.beans.KRSessionEJB;
import com.logicacmg.koa.kr.beans.KRSessionEJBHome;
import com.logicacmg.koa.kr.beans.Kiezers;
import com.logicacmg.koa.kr.beans.KiezersHome;
import com.logicacmg.koa.kr.beans.KiezersKey;
import com.logicacmg.koa.kr.beans.Transactioncode;
import com.logicacmg.koa.kr.beans.TransactioncodeHome;
import com.logicacmg.koa.security.KOAEncryptionUtil;
import com.logicacmg.koa.security.KOAPublicKey;
import com.logicacmg.koa.security.RandomGenerator;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: StemprocesSessionEJB
 */
public class StemprocesSessionEJBBean implements javax.ejb.SessionBean
{
	private final static String STEMPROCES = "STEMPROCES";
	private javax.ejb.SessionContext mySessionCtx;
	/**
	 * getSessionContext
	 */
	public javax.ejb.SessionContext getSessionContext()
	{
		return mySessionCtx;
	}
	/**
	 * setSessionContext
	 */
	public void setSessionContext(javax.ejb.SessionContext ctx)
	{
		mySessionCtx = ctx;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
	}
	/**
	 * ejbCreate
	 */
	public void ejbCreate() throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove()
	{
	}
	/** 
	 * This method performs functional validations on the vote
	 * 
	 * @return boolean - True, all functional validations passed succesfully
	 * 					 false , one ore more validations failed
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private StemTransactie validateVote(
		Stem xStem,
		Kiezers xKiezer,
		StemTransactie xStemTransactie)
		throws com.logicacmg.koa.exception.KOAException
	{
		StemTransactie xTransactie = xStemTransactie;
		try
		{
			//check if input params are OK
			if (xStem == null
				|| xKiezer == null
				|| xKiezer.getKieskringnummer() == null
				|| xStem.kandidaat == null
				|| xStem.kandidaat.kandidaatcodes == null
				|| xStem.kandidaat.kandidaatcodes.size() == 0
				|| xStem.kandidaat.kandidaatcodes.get(0) == null)
			{
				/* check if the candidate is not provided, because we should return different code */
				if (xStem != null
					&& (xStem.kandidaat == null
						|| xStem.kandidaat.kandidaatcodes == null
						|| xStem.kandidaat.kandidaatcodes.size() == 0
						|| xStem.kandidaat.kandidaatcodes.get(0) == null))
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[StemprocesSessionEJB] Missing candidate in the input paramaters(), invalid candidate...");
					xTransactie.VoteStatus = StemTransactie.INVALID_CANDIDATE;
					return xTransactie;
				}
				/* check if the voter is not provided, because we should return different code */
				if (xKiezer == null || xKiezer.getKieskringnummer() == null)
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[StemprocesSessionEJB] Missing voter in the input paramaters(), invalid voter...");
					xTransactie.VoteStatus = StemTransactie.INVALID_CREDENTIALS;
					return xTransactie;
				}
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[StemprocesSessionEJB] Missing data in the input paramaters()...");
				xTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
				return xTransactie;
			}
			//retrieve kandidaat object
			Kandidaat xKandidaat = xStem.kandidaat;
			if (xKandidaat == null)
			{
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[StemprocesSessionEJB] Unable to retrieve kandidaat");
				xTransactie.VoteStatus = StemTransactie.INVALID_CANDIDATE;
				return xTransactie;
			}
			//check if the Stem.kandidaatcode is valid for the kieskring of the kiezer.
			if (!xKiezer
				.getKieskringnummer()
				.equals(xKandidaat.kieskringnummer))
			{
				//Stem.kandidaatcode isn't valid for the kieskring of the kiezer.
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[StemprocesSessionEJB] Stem.kandidaatcode isn't valid for the kieskring of the kiezer.");
				xTransactie.VoteStatus = StemTransactie.INVALID_CANDIDATE;
				return xTransactie;
			}
		}
		catch (java.rmi.RemoteException xRmiExc)
		{
			String[] params = { "Kiezer EJB" };
			KOALogHelper.logErrorCode(
				"[StemprocesSessionEJB]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRmiExc);
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		//all functional validations are ok
		return xTransactie;
	}
	/**
	 * This method encrypts a vote on base of an uncnrypted stem object and 
	 * returns an encryptes stem object
	 * 
	 * @param Stem stem uncrypted Stem object to be crypted
	 * 
	 * @return EncryptedStem object that contains the encrypted vote 
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private EncryptedStem encryptStem(Stem xStem)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] enter encryptStem()");
		EncryptedStem xEncryptedStem = new EncryptedStem();
		StringBuffer sBuffer =
			new StringBuffer().append(
				(String) xStem.kandidaat.kandidaatcodes.get(0));
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.achterNaam);
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.voorletters);
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.positienummer);
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.districtnummer);
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.kieslijstnummer);
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.lijstnaam);
		sBuffer.append(VoteConstants.VOTE_FIELD_SEPARATOR);
		sBuffer.append(xStem.kandidaat.kieskringnummer);
		//encrypt the string with the public key
		xEncryptedStem.encryptedVote =
			KOAEncryptionUtil.encrypt(
				KOAPublicKey.getPublicKey(),
				sBuffer.toString());
		//return it			
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] leaving encryptStem()");
		return xEncryptedStem;
	}
	/**
	 * This method retrieves an instance from the KR SessionBean
	 * 
	 * @return KRSessionEJB object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 * 
	 */
	private KRSessionEJB getKRSessionBean()
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Entering getKRSessionBean()");
		KRSessionEJB xKRBean = null;
		try
		{
			KRSessionEJBHome xKRSessionEJBHome =
				ObjectCache.getInstance().getKRSessionHome();
			xKRBean = xKRSessionEJBHome.create();
		}
		catch (javax.ejb.CreateException xCreateException)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xCreateException.getMessage());
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Exit getKRSessionBean()");
		return xKRBean;
	}
	/**
	 * This method handles the flow of the voting
	 * 
	 * @param Stem - This object contains data about the person a kiezer has voted for
	 * @param Stemcode - The stemcode of the voter
	 * @param Wachtwoord - The wachtwoord of the voter
	 * 
	 * @return StemTransactie - The object contains the state of the vote
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException is thrown whem something has gone wrong.
	 */
	public StemTransactie vote(
		Stem xStem,
		String sStemcode,
		String sWachtwoord)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Entering vote()");
		/*
		 * We can not vote if not all input parameters have
		 * at least some value.
		 */
		if (sStemcode == null
			|| sStemcode.trim().length() == 0
			|| sWachtwoord == null
			|| sWachtwoord.trim().length() == 0
			|| xStem == null)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[StemprocesSessionEJB] One or more input parameters are invalid");
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		// check if stemcode only consists of digits
		for (int i = 0; i < sStemcode.length(); i++)
		{
			char cCharFromStemcode = sStemcode.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromStemcode))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[StemprocesSessionEJBBean] Stemcode is niet numeriek");
				throw new KOAException(
					ErrorConstants.VERIFY_STEM_CODE_NUMERIC_ERR);
			}
		}
		// check if stemcode is exactly 9 digits
		if (sStemcode.length() != 9)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[StemprocesSessionEJBBean] Stemcode bestaat niet uit precies 9 karakters");
			throw new KOAException(ErrorConstants.VERIFY_STEM_CODE_ERR);
		}
		StemTransactie xStemTransactie = new StemTransactie();
		xStemTransactie.VoteStatus = StemTransactie.OK;
		try
		{
			/*
			 * Lets find the kiezer with the provided stemcode
			 */
			KiezersHome xKiezersHome =
				ObjectCache.getInstance().getKiezersHome();
			Kiezers xKiezer =
				xKiezersHome.findByPrimaryKey(new KiezersKey(sStemcode));
			/*
			 * If we did not find a kiezer with this stemcode,
			 * we log this occurence and return immediately
			 */
			if (xKiezer == null)
			{
				xStemTransactie.VoteStatus = StemTransactie.INVALID_CREDENTIALS;
				KOALogHelper.audit(
					KOALogHelper.WARNING,
					AuditEventListener.VOTER,
					ComponentType.STEM,
					"Onbekende stemcode",
					"Een kiezer met stemcode ["
						+ sStemcode
						+ "]heeft getracht in te loggen via modaliteit "
						+ xStem.modaliteit
						+ " met onbekende stemcode.");
				return xStemTransactie;
			}
			/*
			 * We need to verify the state of the system, as one
			 * can only vote if the system is OPEN for voting.
			 * We also need to check the kiezer his/her credentials.
			 */
			xStemTransactie =
				verifyKiezer(xKiezer, sStemcode, sWachtwoord, xStem.modaliteit);
			/*
			 * If not all went well we exit without voting
			 */
			if (xStemTransactie.VoteStatus != StemTransactie.OK)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[StemprocesSessionEJB] Exit vote()");
				return xStemTransactie;
			}
			xStemTransactie = validateVote(xStem, xKiezer, xStemTransactie);
			/*
			 * If not all went well we exit without voting
			 */
			if (xStemTransactie.VoteStatus != StemTransactie.OK)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[StemprocesSessionEJB] Exit vote()");
				return xStemTransactie;
			}
			//encryptVote
			EncryptedStem xEncryptedStem = encryptStem(xStem);
			if (xEncryptedStem != null)
			{
				xKiezer.setTimestampGestemd(
					new java.sql.Timestamp(System.currentTimeMillis()));
				xKiezer.setModaliteit(xStem.modaliteit);
				/* save the vote encrypted and set the transactioncode */
				xStemTransactie.Transactienummer =
					saveEncryptedVote(xEncryptedStem, xKiezer);
				/* if we did not get a transactionnumber */
				if (xStemTransactie.Transactienummer == null
					|| xStemTransactie.Transactienummer.trim().length() == 0)
				{
					xStemTransactie.VoteStatus = StemTransactie.VOTING_FAILED;
					/* Use transaction of the  voting for writing audit messages */
					KOALogHelper.auditTX(
						KOALogHelper.TRACE,
						AuditEventListener.VOTER,
						STEMPROCES,
						"Stemcode " + xStemTransactie.Stemcode,
						"De kiezer met stemcode "
							+ xStemTransactie.Stemcode
							+ " heeft NIET succesvol een stem uit kunnen brengen via modaliteit "
							+ xStem.modaliteit
							+ ".");
				}
				else
				{
					/* Zet ook de timestamp en het channel op de stemtransactie die teruggegeven wordt */
					xStemTransactie.VotingTime =
						(Date) xKiezer.getTimestampGestemd();
					xStemTransactie.Modaliteit = xStem.modaliteit;
					xStemTransactie.VoteStatus = StemTransactie.OK;
					KOALogHelper.auditTX(
						KOALogHelper.TRACE,
						AuditEventListener.VOTER,
						STEMPROCES,
						"Stemcode " + xStemTransactie.Stemcode,
						"De kiezer met stemcode "
							+ xStemTransactie.Stemcode
							+ " heeft succesvol gestemd via modaliteit "
							+ xStem.modaliteit
							+ ". De transactiecode is: "
							+ xStemTransactie.Transactienummer);
				}
			}
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[StemprocesSessionEJB] Unable to process voting flow.");
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		catch (javax.ejb.FinderException xFinderExc)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"[StemprocesSessionEJB]",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderExc);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Exit vote()");
		return xStemTransactie;
	}
	/**
	 * Verifies if a kiezer , indicated biy param sStemcode is valid
	 * 
	 * @param xKiezer - The kiezer entity bean
	 * @param sStemcode - The stemcode of the kiezer
	 * @param sWachtwoord - the plain value of the kiezers password
	 * 
	 * @return Stemtransactie data object
	 */
	private StemTransactie verifyKiezer(
		Kiezers xKiezer,
		String sStemcode,
		String sWachtwoord,
		String sModaliteit)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] entering verifyKiezer()");
		StemTransactie xStemTransactie = new StemTransactie();
		xStemTransactie.Stemcode = sStemcode;
		xStemTransactie.VoteStatus = StemTransactie.OK;
		try
		{
			/*
			 * Check the state of the system.
			 * If the state is not OPEN, the kiezer is not
			 * allowed to vote.
			 */
			KRSessionEJB xKRSession = getKRSessionBean();
			String sCurrentState = xKRSession.getCurrentSystemState();
			if (!sCurrentState.equals(SystemState.OPEN))
			{
				if (sCurrentState.equals(SystemState.BLOCKED))
				{
					xStemTransactie.VoteStatus =
						StemTransactie.ELECTION_BLOCKED;
				}
				else if (
					sCurrentState.equals(SystemState.SUSPENDED)
						|| sCurrentState.equals(SystemState.RE_INITIALIZED))
				{
					xStemTransactie.VoteStatus =
						StemTransactie.ELECTION_SUSPENDED;
				}
				else if (
					sCurrentState.equals(SystemState.PREPARE)
						|| sCurrentState.equals(SystemState.INITIALIZED))
				{
					xStemTransactie.VoteStatus =
						StemTransactie.ELECTION_NOT_YET_OPEN;
				}
				else
				{
					xStemTransactie.VoteStatus = StemTransactie.ELECTION_CLOSED;
				}
				return xStemTransactie;
			}
			//check if password is correct
			String sHashedPassword =
				KOAEncryptionUtil.hashPassword(sWachtwoord);
			String sKiezerPassword = xKiezer.getHashedwachtwoord();
			if (sKiezerPassword == null
				|| !sKiezerPassword.equals(sHashedPassword))
			{
				/* set the return value */
				xStemTransactie.VoteStatus = StemTransactie.INVALID_CREDENTIALS;
				KOALogHelper.audit(
					KOALogHelper.WARNING,
					AuditEventListener.VOTER,
					ComponentType.KR,
					"Stemcode " + sStemcode,
					"De kiezer met stemcode ["
						+ sStemcode
						+ "] heeft getracht in te loggen via modaliteit "
						+ sModaliteit
						+ " met een incorrecte toegangscode.");
			}
			// check if kiezer is not blocked 
			if (xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				Boolean bAccountLocked = xKiezer.getAccountlocked();
				Timestamp tsTimestamp = xKiezer.getTimestampunlock();
				if ((bAccountLocked != null && bAccountLocked.booleanValue())
					&& (tsTimestamp != null
						&& (tsTimestamp.getTime() >= System.currentTimeMillis())))
				{
					/* Adding audit message for account locked */
					KOALogHelper.audit(
						KOALogHelper.WARNING,
						AuditEventListener.VOTER,
						ComponentType.KR,
						"Stemcode " + sStemcode,
						"De kiezer met stemcode ["
							+ sStemcode
							+ "] heeft getracht in te loggen via modaliteit "
							+ sModaliteit
							+ ", terwijl de stemcode geblokkeerd is.");
					xStemTransactie.VoteStatus = StemTransactie.ACCOUNT_LOCKED;
				}
				else
				{
					xKiezer.setAccountlocked(new Boolean(false));
					/* reset the timestamp for unlocking  */
					xKiezer.setTimestampunlock(null);
				}
			}
			/* check if kiezer hasn't voted yet */
			if (xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				Boolean bAlreadyVoted = xKiezer.getReedsgestemd();
				if (bAlreadyVoted == null
					|| bAlreadyVoted.equals(Boolean.TRUE))
				{
					xStemTransactie.VoteStatus = StemTransactie.ALREADY_VOTED;
					xStemTransactie.Transactienummer =
						xKiezer.getTransactienummer();
					/* Adding audit message for invalid credentials */
					KOALogHelper.audit(
						KOALogHelper.WARNING,
						AuditEventListener.VOTER,
						ComponentType.KR,
						"Stemcode " + sStemcode,
						"De kiezer met stemcode ["
							+ sStemcode
							+ "] heeft reeds gestemd en probeert nogmaals een stem uit te brengen via modaliteit "
							+ sModaliteit
							+ ".");
				}
			}
			/* check if the account is marked as deleted */
			if (xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				Boolean bDeleted = xKiezer.getVerwijderd();
				if (bDeleted != null && bDeleted.equals(Boolean.TRUE))
				{
					/* say the account is locked */
					xStemTransactie.VoteStatus = StemTransactie.KIEZER_DELETED;
				}
			}
			/* if none of the above, we can say verification is succesfull */
			xStemTransactie.VotingTime = xKiezer.getTimestampGestemd();
			xStemTransactie.Modaliteit = xKiezer.getModaliteit();
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"[StemprocesSessionEJB]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] leaving verifyKiezer()");
		return xStemTransactie;
	}
	/**
	 * This method retrieves the next transactioncode from
	 * the database. 
	 * 
	 * NOTE: This method must be set to transaction isolation: serialized
	 * because we must _never_ return the same transactioncode 
	 * to a different voter
	 * 
	 * @return String the next transactioncode
	 * @throws KOAException when no transactioncode is found
	 */
	public String getNextTransactionCode() throws KOAException
	{
		/* get the next code */
		BigDecimal xTxCode = RandomGenerator.getInstance().getRandomNumber(9);
		BigDecimal xAdd = new BigDecimal(1);
		TransactioncodeHome xTransactioncodeHome =
			ObjectCache.getInstance().getTransactioncodeHome();
		int iCounter = 0;
		int iMax =
			TechnicalProps.getIntProperty(TechnicalProps.MAX_RANDOM_ATTEMPTS);
		while (iCounter < iMax)
		{
			try
			{
				//check if Tx Number already exists
				Transactioncode xTransactioncode =
					xTransactioncodeHome.create(xTxCode.toString());
				//if it doesn't exists yet, mark it as already used.
				xTransactioncode.setAlreadyused(true);
				//set counter to max to escape from while loop
				iCounter = iMax;
			}
			catch (javax.ejb.DuplicateKeyException xDuplicateKeyException)
			{
				//current tx number already exists
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"Found duplicate key, trying to retrieve a new one");
				//add 1 to the previous tx-code
				xTxCode = xTxCode.add(xAdd);
				//check if max number of attempts is reached
				if (iCounter == iMax)
				{
					//if so, log it and throw a KOAException
					KOALogHelper.log(
						KOALogHelper.WARNING,
						"unable to create a new unique transactioncode for voter");
					throw new KOAException(
						ErrorConstants.VOTER_EXECUTE_VOTE_ERROR);
				}
			}
			catch (javax.ejb.CreateException xCreateException)
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					xCreateException.getMessage());
				throw new KOAException(
					ErrorConstants.VOTER_EXECUTE_VOTE_ERROR,
					xCreateException);
			}
			catch (java.rmi.RemoteException xRemoteExc)
			{
				KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
				throw new KOAException(
					ErrorConstants.VOTER_EXECUTE_VOTE_ERROR,
					xRemoteExc);
			}
			//increase attempts counter
			iCounter++;
		}
		/* return the transactioncode */
		return xTxCode.toString();
	}
	/**
	 * This method sores the encrypted vote in the ESB and marks the user as already voted
	 * 
	 * Note : This method has to cinfigured as on single transaction !!!
	 * 
	 * @param EncryptedVote - The encrypte vote object to be stored
	 * 
	 * @return String the transactioncode which belongs to this vote
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 * 
	 * Before OR22.3.93:
	 * @return boolean - True if the updates are succesfully
	 *                   False when the updates aren't stored
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private String saveEncryptedVote(
		EncryptedStem xEncryptedVote,
		Kiezers xKiezer)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Entering saveEncryptedVote()");
		String txCode = null;
		try
		{
			/* fetch the next transaction code */
			txCode = getNextTransactionCode();
			/* set the transactioncode in the kiezer */
			xKiezer.setTransactienummer(txCode);
			/* mark the kiezer as already voted */
			xKiezer.setReedsgestemd(new Boolean(true));
			//store encrypted vote
			ESBSessionEJBHome xESBSessionEJBHome =
				ObjectCache.getInstance().getESBSessionEJBHome();
			ESBSessionEJB xESBSessionEJB = xESBSessionEJBHome.create();
			xESBSessionEJB.saveEncryptedVote(xEncryptedVote);
		}
		catch (javax.ejb.CreateException xCreateException)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xCreateException.getMessage());
			throw new KOAException(
				ErrorConstants.VOTER_EXECUTE_VOTE_ERROR,
				xCreateException);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(
				ErrorConstants.VOTER_EXECUTE_VOTE_ERROR,
				xRemoteExc);
		}
		catch (KOAException koae)
		{
			KOALogHelper.log(KOALogHelper.ERROR, koae.getMessage());
			throw new KOAException(
				ErrorConstants.VOTER_EXECUTE_VOTE_ERROR,
				koae);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Exit saveEncryptedVote()");
		return txCode;
	}
	/**
	 * This method retrieves an Kandidaatcode object by it's primary key.
	 * 
	 * @param sKandidaatcode - The primary key of the kandidaat to search for.
	 * 
	 * @return Kandidaatcodes object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public Kandidaat getKandidaat(String sKandidaatcode)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Entering getKandidaat()");
		Kandidaat xKandidaat = null;
		try
		{
			KiesLijstHome xKiesLijstHome =
				ObjectCache.getInstance().getKiesLijstHome();
			KiesLijst xKiesLijst = xKiesLijstHome.create();
			if (xKiesLijst != null)
			{
				xKandidaat = xKiesLijst.getKandidaat(sKandidaatcode);
			}
		}
		catch (javax.ejb.CreateException xCreateException)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xCreateException.getMessage());
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(ErrorConstants.STEMPROCES_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Exit getKandidaat()");
		return xKandidaat;
	}
}