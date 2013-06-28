/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.kieslijst.beans.KiesLijstBean.java
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
  *  0.1		18-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.kieslijst.beans;
import java.rmi.RemoteException;
import java.sql.Timestamp;
import java.util.Enumeration;
import java.util.Vector;

import com.logica.eplatform.error.ErrorMessageFactory;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.dataobjects.Fingerprint;
import com.logicacmg.koa.dataobjects.Kandidaat;
import com.logicacmg.koa.dataobjects.KandidaatResponse;
import com.logicacmg.koa.dataobjects.KiesLijstFingerprintCompareResult;
import com.logicacmg.koa.dataobjects.Partij;
import com.logicacmg.koa.db.FingerPrintDB;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.koaschema.Kandidaatcodes;
import com.logicacmg.koa.koaschema.KandidaatcodesHome;
import com.logicacmg.koa.koaschema.KandidaatcodesKey;
import com.logicacmg.koa.koaschema.KieskringenKey;
import com.logicacmg.koa.koaschema.Kieslijsten;
import com.logicacmg.koa.koaschema.KieslijstenHome;
import com.logicacmg.koa.koaschema.KieslijstenKey;
import com.logicacmg.koa.koaschema.Lijstposities;
import com.logicacmg.koa.koaschema.LijstpositiesHome;
import com.logicacmg.koa.koaschema.LijstpositiesKey;
import com.logicacmg.koa.kr.beans.Kiezers;
import com.logicacmg.koa.kr.beans.KiezersHome;
import com.logicacmg.koa.kr.beans.KiezersKey;
import com.logicacmg.koa.security.KOAEncryptionUtil;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: KiesLijst
 */
public class KiesLijstBean implements javax.ejb.SessionBean
{
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
	 * This methods retrieves all the kieslijsten(partijen) foe a given kieskring
	 * 
	 * @param String sKieskringnummer The id of the kieskring to retrieve the kieslijsten for.
	 * @return Vector containing Partij objects
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public Vector getPartijen(String sKieskringnummer)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[StemprocesSessionEJB] Entering getPartijen()");
		Vector xPartyVector = new Vector();
		if (sKieskringnummer == null)
		{
			return null;
		}
		try
		{
			KieslijstenHome xKieslijstenHome =
				ObjectCache.getInstance().getKieslijstenHome();
			Enumeration xEnum =
				xKieslijstenHome.findKieslijstenByFk_kkr_1(
					new KieskringenKey(sKieskringnummer));
			while (xEnum.hasMoreElements())
			{
				Kieslijsten xKieslijst = (Kieslijsten) xEnum.nextElement();
				if (xKieslijst != null)
				{
					Partij xPartij = new Partij();
					xPartij.naam = xKieslijst.getLijstnaam();
					xPartij.kieskringnummer = sKieskringnummer;
					KieslijstenKey xKieslijstenKey =
						(KieslijstenKey) xKieslijst.getPrimaryKey();
					if (xKieslijstenKey != null)
					{
						xPartij.kieslijstnummer =
							xKieslijstenKey.kieslijstnummer;
					}
					xPartyVector.add(xPartij);
				}
			}
		}
		catch (javax.ejb.FinderException xCreateException)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xCreateException.getMessage());
			throw new KOAException(ErrorConstants.KLB_PARTIJEN_ERR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(ErrorConstants.KLB_PARTIJEN_ERR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesLijstBean] Exit getPartijen()");
		return xPartyVector;
	}
	/**
	 * This methods retrieves all the candidates for a given kieslijst
	 * 
	 * @param String sKieslijstnummer The id of the kieslijst to retrieve the candidates for.
	 * @param String sKieskringnummer The id of the  kieskring to which the kieslijst belongs.
	 * 
	 * @return Vector containing Kandidaat objects
	 * 
	 * @exception com.logicacmg.exception.KOAException
	 */
	public Vector getKandidaten(
		String sKieslijstnummer,
		String sKieskringnummer)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesLijstBean] Entering getKandidaten()");
		Vector xCandidateVector = new Vector();
		if (sKieslijstnummer == null || sKieskringnummer == null)
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KiesLijstBean] PARAM IS NULL");
			return null;
		}
		try
		{
			LijstpositiesHome xLijstpositiesHome =
				ObjectCache.getInstance().getLijstpositiesHome();
			Enumeration xEnum =
				xLijstpositiesHome.findLijstpositiesByFk_klkr_1(
					new KieslijstenKey(
						sKieslijstnummer,
						new KieskringenKey(sKieskringnummer)));
			while (xEnum.hasMoreElements())
			{
				Lijstposities xLijstposities =
					(Lijstposities) xEnum.nextElement();
				if (xLijstposities != null)
				{
					Kandidaat xKandidaat = new Kandidaat();
					xKandidaat.achterNaam = xLijstposities.getAchternaam();
					xKandidaat.voorletters = xLijstposities.getVoorletters();
					xKandidaat.roepNaam = xLijstposities.getRoepnaam();
					xKandidaat.geslacht = xLijstposities.getGeslacht();
					xKandidaat.woonplaats = xLijstposities.getWoonplaats();
					xKandidaat.kieskringnummer = sKieskringnummer;
					xKandidaat.kieslijstnummer = sKieslijstnummer;
					LijstpositiesKey xKey =
						(LijstpositiesKey) xLijstposities.getPrimaryKey();
					xKandidaat.positienummer = xKey.positienummer;
					Enumeration xKandidaatcodeEnum =
						xLijstposities.getKandidaatcodes();
					xKandidaat.kandidaatcodes = new Vector();
					while (xKandidaatcodeEnum.hasMoreElements())
					{
						Kandidaatcodes xKandidaatcode =
							(Kandidaatcodes) xKandidaatcodeEnum.nextElement();
						if (xKandidaatcode != null)
						{
							KandidaatcodesKey xKandidaatcodesKey =
								(KandidaatcodesKey) xKandidaatcode
									.getPrimaryKey();
							xKandidaat.kandidaatcodes.add(
								xKandidaatcodesKey.kandidaatcode);
						}
					}
					xCandidateVector.add(xKandidaat);
				}
			}
		}
		catch (javax.ejb.FinderException xFinderException)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				xFinderException.getMessage());
			throw new KOAException(ErrorConstants.KLB_KANDIDATEN_ERR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(ErrorConstants.KLB_KANDIDATEN_ERR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesLijstBean] Exit getKandidaten()");
		return xCandidateVector;
	}
	/**
	 * This method verifys if a given candidate exists
	 * 
	 * @param sKandidaatnummer - The id of the candidate to search for.
	 * @param sStemcode - The id of the voter.
	 * 
	 * @return KandidaatResponse object that indicates that the given sKandidaatnummer is valid or not.
	 * 
	 * @exception com.logicacmg.exception.KOAException
	 */
	public KandidaatResponse verifyKandidaat(
		String sKandidaatcode,
		String sStemcode)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesLijstBean] Entering VerifyKandidaat()");
		KandidaatResponse xKandidaatResponse = new KandidaatResponse();
		/*
		 * If the kandidaatcode is not present (null or empty)
		 * we return immediately after setting the response
		 * to KANDIDATE NOT FOUND and also logging the fact
		 * in the audit log
		 */
		if (sKandidaatcode == null || sKandidaatcode.equals(""))
		{
			xKandidaatResponse.status = KandidaatResponse.KANDIDATE_NOT_FOUND;
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.VOTER,
				"KiesLijst",
				"Stemcode " + sStemcode,
				"De kiezer met stemcode ["
					+ sStemcode
					+ "] heeft een lege kandidaatcode ingevoerd.");
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KiesLijstBean] kandidaat code is null");
			return xKandidaatResponse;
		}
		// Check if kandidaatcode only consists of digits
		for (int i = 0; i < sKandidaatcode.length(); i++)
		{
			char cCharFromKandidaatcode = sKandidaatcode.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromKandidaatcode))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[KiesLijstBean] kandidaat code is niet numeriek");
				xKandidaatResponse.status =
					KandidaatResponse.KANDIDATE_NOT_NUMERIC;
				return xKandidaatResponse;
			}
		}
		// Check if kandidaat code is no longer then 9 digits
		if (sKandidaatcode.length() != 9)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KiesLijstBean] kandidaat code bestaat niet uit 9 karakters");
			xKandidaatResponse.status =
				KandidaatResponse.KANDIDATE_NOT_CORRECT_LENGTH;
			return xKandidaatResponse;
		}
		if (sStemcode == null)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KiesLijstBean] Stemcode is null");
			throw new KOAException(ErrorConstants.VERIFY_CANDIDATE_ERR);
		}
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KiesLijstBean] lookup controller.");
			ControllerHome controllerHome =
				ObjectCache.getInstance().getControllerHome();
			/* get current state from controller */
			Controller controller = controllerHome.create();
			KOALogHelper.log(KOALogHelper.TRACE, "[KiesLijstBean] get state.");
			/* only valid if status=open */
			String sCurrentState = controller.getCurrentState();
			if (!SystemState.OPEN.equals(sCurrentState))
			{
				/* throw exception which indicates elections are closed */
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KiesLijstBean] Kandidaat not found, election not open.");
				if (sCurrentState.equals(SystemState.BLOCKED))
				{
					xKandidaatResponse.status =
						KandidaatResponse.ELECTION_BLOCKED;
				}
				else if (sCurrentState.equals(SystemState.SUSPENDED))
				{
					xKandidaatResponse.status =
						KandidaatResponse.ELECTION_SUSPENDED;
				}
				else if (
					sCurrentState.equals(SystemState.PREPARE)
						|| sCurrentState.equals(SystemState.INITIALIZED))
				{
					xKandidaatResponse.status =
						KandidaatResponse.ELECTION_NOT_YET_OPEN;
				}
				else
				{
					xKandidaatResponse.status =
						KandidaatResponse.ELECTION_CLOSED;
				}
				return xKandidaatResponse;
			}
		}
		catch (CreateException ce)
		{
			KOALogHelper.log(KOALogHelper.ERROR, ce.getMessage());
			throw new KOAException(ErrorConstants.VERIFY_CANDIDATE_ERR, ce);
		}
		catch (RemoteException re)
		{
			KOALogHelper.log(KOALogHelper.ERROR, re.getMessage());
			throw new KOAException(ErrorConstants.VERIFY_CANDIDATE_ERR, re);
		}
		// Find the kieskring for the Stemcode	
		try
		{
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KiesLijstBean] get kiezershome.");
			KiezersHome xKiezersHome =
				ObjectCache.getInstance().getKiezersHome();
			KiezersKey xKiezersKey = new KiezersKey(sStemcode);
			Kiezers xKiezer = xKiezersHome.findByPrimaryKey(xKiezersKey);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KiesLijstBean] get kandidaat.");
			Kandidaat xKandidaat = getKandidaat(sKandidaatcode);
			if (xKandidaat == null)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KiesLijstBean] Kandidaat niet gevonden");
				xKandidaatResponse.status =
					KandidaatResponse.KANDIDATE_NOT_FOUND;
				KOALogHelper.audit(
					KOALogHelper.TRACE,
					AuditEventListener.VOTER,
					"KiesLijst",
					"Stemcode " + sStemcode,
					"De kiezer met stemcode ["
						+ sStemcode
						+ "] heeft een onbekende kandidaatcode ingevoerd.");
			}
			else if (xKiezer == null)
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KiesLijstBean] Kiezer niet gevonden");
				xKandidaatResponse.status =
					KandidaatResponse.KANDIDATE_NOT_FOUND;
			}
			else if (
				xKandidaat.kieskringnummer.equals(xKiezer.getKieskringnummer())
					&& xKandidaat.achterNaam != null
					&& xKandidaat.achterNaam.trim().length() > 0)
			{
				xKandidaatResponse.status = KandidaatResponse.KANDIDATE_OK;
				xKandidaatResponse.kandidaatcode = sKandidaatcode;
				xKandidaatResponse.kandidaat = xKandidaat;
			}
			else
			{
				KOALogHelper.audit(
					KOALogHelper.TRACE,
					AuditEventListener.VOTER,
					"KiesLijst",
					"Stemcode " + sStemcode,
					"De kiezer met stemcode ["
						+ sStemcode
						+ "] heeft een kandidaatcode ["
						+ sKandidaatcode
						+ "] ingevoerd, welke niet geldig is voor deze kiezer.");
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KiesLijstBean] Kandidaat niet gevonden binnen de kieskring");
				xKandidaatResponse.status =
					KandidaatResponse.KANDIDATE_NOT_FOUND;
			}
		}
		catch (FinderException fe)
		{
			KOALogHelper.log(KOALogHelper.ERROR, fe.getMessage());
			throw new KOAException(ErrorConstants.VERIFY_CANDIDATE_ERR, fe);
		}
		catch (RemoteException re)
		{
			KOALogHelper.log(KOALogHelper.ERROR, re.getMessage());
			throw new KOAException(ErrorConstants.VERIFY_CANDIDATE_ERR, re);
		}
		return xKandidaatResponse;
	}
	/**
	 * This method retrieves an Kandiddaatcode object by it's primmary key.
	 * 
	 * @param sKandidaatcode - The primary key of the kandidaat to search for.
	 * 
	 * @return Kandidaatcodes object
	 * 
		 * @exception com.logicacmg.exception.KOAException
	 */
	public Kandidaat getKandidaat(String sKandidaatcode)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesLijstBean] Entering getKandidaat()");
		if (sKandidaatcode == null)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KiesLijstBean] input parameter is null");
			throw new KOAException(ErrorConstants.KLB_KANDIDAAT_ERR);
		}
		Kandidaat xKandidaat = null;
		try
		{
			KandidaatcodesHome xKandidaatcodesHome =
				ObjectCache.getInstance().getKandidaatcodesHome();
			Kandidaatcodes xKandidaatcodes =
				xKandidaatcodesHome.findByPrimaryKey(
					new KandidaatcodesKey(sKandidaatcode));
			if (xKandidaatcodes != null)
			{
				//Kandidaat.naam 	
				Lijstposities xLijstposities =
					xKandidaatcodes.getFk_kkrklpn_1();
				xKandidaat = new Kandidaat();
				xKandidaat.achterNaam = xLijstposities.getAchternaam();
				xKandidaat.voorletters = xLijstposities.getVoorletters();
				xKandidaat.roepNaam = xLijstposities.getRoepnaam();
				xKandidaat.geslacht = xLijstposities.getGeslacht();
				xKandidaat.woonplaats = xLijstposities.getWoonplaats();
				LijstpositiesKey xLijstpositiesKey =
					(LijstpositiesKey) xLijstposities.getPrimaryKey();
				xKandidaat.positienummer = xLijstpositiesKey.positienummer;
				xKandidaat.kieskringnummer =
					xLijstpositiesKey.fk_klkr_1_fk_kkr_1_kieskringnummer;
				xKandidaat.kieslijstnummer =
					xLijstpositiesKey.fk_klkr_1_kieslijstnummer;
				//retrieve lijstnaam
				Kieslijsten xKieslijsten = xLijstposities.getFk_klkr_1();
				xKandidaat.lijstnaam = xKieslijsten.getLijstnaam();
				KandidaatcodesKey xKandidaatcodesKey =
					(KandidaatcodesKey) xKandidaatcodes.getPrimaryKey();
				if (xKandidaatcodesKey.kandidaatcode != null)
				{
					xKandidaat.kandidaatcodes = new Vector();
					xKandidaat.kandidaatcodes.add(
						xKandidaatcodesKey.kandidaatcode);
				}
			}
		}
		catch (javax.ejb.FinderException xFinderException)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				xFinderException.getMessage());
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KiesLijstBean] Kandidaat niet gevonden (finder exception)");
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.ERROR, xRemoteExc.getMessage());
			throw new KOAException(ErrorConstants.KLB_KANDIDAAT_ERR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesLijstBean] Exit getKandidaat()");
		return xKandidaat;
	}
	/**
	 * Save the fingerprint of the current kieslijst database tables 
	 * in the database
	 * 
	 * @throws KOAException Exception when something goes wrong during save of the fingerprint.
	 * 
	 */
	public void saveCurrentKieslijstFingerprints() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.saveCurrentKieslijstFingerprints] Start saving fingerprints for candidates...");
		String sMessage =
			this.getMessage(
				ErrorConstants.FINGERPRINT_CREATE_KIESLIJST_FINGERPRINTS,
				null);
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.FINGERPRINT,
			"KiesLijst.saveFingerprints",
			"Systeem",
			sMessage);
		/* init variables */
		FingerPrintDB xFPDB = new FingerPrintDB();
		/* create the current fingerprint for kandidaatcodes */
		Fingerprint xKandidaatCodeFP =
			this.createCurrentKandidaatCodesFingerprint();
		/* create the current fingerprint for lijstposities */
		Fingerprint xLijstpositiesFP =
			this.createCurrentLijstpositiesFingerprint();
		/* create the current fingerprint for kieslijsten */
		Fingerprint xKieslijstFP = this.createCurrentKieslijstFingerprint();
		/* save the fingerprints in the database */
		xFPDB.insertKiesLijstFingerprint(xKandidaatCodeFP);
		xFPDB.insertKiesLijstFingerprint(xLijstpositiesFP);
		xFPDB.insertKiesLijstFingerprint(xKieslijstFP);
	}
	/**
	 * Compare the current fingerprint of the kieslijst tables
	 * with the last saved fingeprint.
	 * 
	 * @return CallResult the result of the compare action
	 * 
	 * @throws KOAException when something goes wrong during the compare
	 * 
	 */
	public KiesLijstFingerprintCompareResult compareKieslijstFingerprint()
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.compareKieslijstFingerprint] Start the check on the kieslijst fingerprints...");
		String sMessage =
			this.getMessage(
				ErrorConstants.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINTS,
				null);
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.FINGERPRINT,
			"KiesLijst.compareFingerprint",
			this.getSessionContext().getCallerPrincipal().getName(),
			sMessage);
		/* init variables */
		KiesLijstFingerprintCompareResult xCallResult =
			new KiesLijstFingerprintCompareResult();
		FingerPrintDB xFPDB = new FingerPrintDB();
		/* create the current fingerprint */
		Fingerprint xCurrentKandidaatCodeFP =
			this.createCurrentKandidaatCodesFingerprint();
		Fingerprint xCurrentLijstpositiesFP =
			this.createCurrentLijstpositiesFingerprint();
		Fingerprint xCurrentKieslijstFP =
			this.createCurrentKieslijstFingerprint();
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.compareKieslijstFingerprint] Got all current fingerprints, getting fingerprints from database...");
		/* get the latest fingerprint from the database */
		Fingerprint xDBKandidaatCodeFP =
			xFPDB.getLatestFingerprint(
				Fingerprint.KIESLIJST_KANDIDAATCODES_FINGERPRINT);
		Fingerprint xDBLijstpositiesFP =
			xFPDB.getLatestFingerprint(
				Fingerprint.KIESLIJST_LIJSTPOSITIES_FINGERPRINT);
		Fingerprint xDBKieslijstFP =
			xFPDB.getLatestFingerprint(
				Fingerprint.KIESLIJST_KIESLIJSTEN_FINGERPRINT);
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.compareKieslijstFingerprint] Got all fingerprints from database, start check on the fingerprints...");
		/* compare the fingerprint */
		boolean bKandidaatCodesEqual =
			xCurrentKandidaatCodeFP.equals(xDBKandidaatCodeFP);
		boolean bLijstpositiesEqual =
			xCurrentLijstpositiesFP.equals(xDBLijstpositiesFP);
		boolean bKieslijstEqual = xCurrentKieslijstFP.equals(xDBKieslijstFP);
		if (bKandidaatCodesEqual)
		{
			String[] params = { "kandidaatcodes" };
			sMessage =
				this.getMessage(
					ErrorConstants
						.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_EQUAL,
					params);
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.FINGERPRINT,
				"KiesLijst.compareFingerprint",
				this.getSessionContext().getCallerPrincipal().getName(),
				sMessage);
		}
		else
		{
			String[] params = { "kandidaatcodes" };
			sMessage =
				this.getMessage(
					ErrorConstants
						.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_DIFFERENT,
					params);
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.FINGERPRINT,
				"KiesLijst.compareFingerprint",
				this.getSessionContext().getCallerPrincipal().getName(),
				sMessage);
		}
		if (bLijstpositiesEqual)
		{
			String[] params = { "lijstposities" };
			sMessage =
				this.getMessage(
					ErrorConstants
						.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_EQUAL,
					params);
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.FINGERPRINT,
				"KiesLijst.compareFingerprint",
				this.getSessionContext().getCallerPrincipal().getName(),
				sMessage);
		}
		else
		{
			String[] params = { "lijstposities" };
			sMessage =
				this.getMessage(
					ErrorConstants
						.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_DIFFERENT,
					params);
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.FINGERPRINT,
				"KiesLijst.compareFingerprint",
				this.getSessionContext().getCallerPrincipal().getName(),
				sMessage);
		}
		if (bKieslijstEqual)
		{
			String[] params = { "kieslijsten" };
			sMessage =
				this.getMessage(
					ErrorConstants
						.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_EQUAL,
					params);
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.FINGERPRINT,
				"KiesLijst.compareFingerprint",
				this.getSessionContext().getCallerPrincipal().getName(),
				sMessage);
		}
		else
		{
			String[] params = { "kieslijsten" };
			sMessage =
				this.getMessage(
					ErrorConstants
						.FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_DIFFERENT,
					params);
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.FINGERPRINT,
				"KiesLijst.compareFingerprint",
				this.getSessionContext().getCallerPrincipal().getName(),
				sMessage);
		}
		/* fill the result object */
		xCallResult.setKandidaatcodesCurrentFP(
			xCurrentKandidaatCodeFP.getFingerprint());
		xCallResult.setLijstpositiesCurrentFP(
			xCurrentLijstpositiesFP.getFingerprint());
		xCallResult.setKieslijstCurrentFP(xCurrentKieslijstFP.getFingerprint());
		xCallResult.setKandidaatcodesDatabaseFP(
			xDBKandidaatCodeFP.getFingerprint());
		xCallResult.setLijstpositiesDatabaseFP(
			xDBLijstpositiesFP.getFingerprint());
		xCallResult.setKieslijstDatabaseFP(xDBKieslijstFP.getFingerprint());
		xCallResult.setKandidaatCodeFPEqual(bKandidaatCodesEqual);
		xCallResult.setLijstpositiesFPEqual(bLijstpositiesEqual);
		xCallResult.setKieslijstFPEqual(bKieslijstEqual);
		/* return the result */
		return xCallResult;
	}
	/**
	 * Creates the current fingerprint of the kandidaatcodes table for the kieslijst
	 * 
	 * @return Fingerprint fingerprint object with the current fingerprint, time and type
	 * 
	 * @throws KOAException Exception when something goes wrong during creation.
	 * 
	 */
	private Fingerprint createCurrentKandidaatCodesFingerprint()
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.createCurrentKandidaatCodesFingerprint] Start creating fingerprints for kandidaatcodes...");
		/* init variables */
		Fingerprint xFingerprint = null;
		String sDataSource =
			JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA);
		/* create the fingerprint */
		byte[] baFingerprint =
			KOAEncryptionUtil.getFingerPrint(
				sDataSource,
				TechnicalProps.KIESLIJST_SCHEMA_NAME,
				TechnicalProps.KIESLIJST_KANDIDAATCODE_TABLE_NAME,
				TechnicalProps.KIESLIJST_KANDIDAATCODE_COLUMNS,
				TechnicalProps.KIESLIJST_KANDIDAATCODE_SORT_KEY);
		/* fill up the object */
		xFingerprint = new Fingerprint();
		xFingerprint.setFingerprint(baFingerprint);
		xFingerprint.setFingerprintType(
			Fingerprint.KIESLIJST_KANDIDAATCODES_FINGERPRINT);
		xFingerprint.setTimestamp(new Timestamp(System.currentTimeMillis()));
		String[] params =
			{
				"kandidaatcodes",
				KOAEncryptionUtil.fingerprintValueToString(baFingerprint)};
		String sMessage =
			this.getMessage(
				ErrorConstants.FINGERPRINT_KIESLIJST_CREATE_SINGLE_FINGERPRINT,
				params);
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.FINGERPRINT,
			"KiesLijst.saveFingerprint",
			"Systeem",
			sMessage);
		/* return xFingerprint */
		return xFingerprint;
	}
	/**
	 * Creates the current fingerprint of the lijstposities of the kieslijst
	 * 
	 * @return Fingerprint fingerprint object with the current fingerprint, time and type
	 * 
	 * @throws KOAException Exception when something goes wrong during creation.
	 * 
	 */
	private Fingerprint createCurrentLijstpositiesFingerprint()
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.createCurrentKandidaatCodesFingerprint] Start creating fingerprints for lijstposities...");
		/* init variables */
		Fingerprint xFingerprint = null;
		String sDataSource =
			JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA);
		/* create the fingerprint */
		byte[] baFingerprint =
			KOAEncryptionUtil.getFingerPrint(
				sDataSource,
				TechnicalProps.KIESLIJST_SCHEMA_NAME,
				TechnicalProps.KIESLIJST_LIJSTPOSITIES_TABLE_NAME,
				TechnicalProps.KIESLIJST_LIJSTPOSITIES_COLUMNS,
				TechnicalProps.KIESLIJST_LIJSTPOSITIES_SORT_KEY);
		/* fill up the object */
		xFingerprint = new Fingerprint();
		xFingerprint.setFingerprint(baFingerprint);
		xFingerprint.setFingerprintType(
			Fingerprint.KIESLIJST_LIJSTPOSITIES_FINGERPRINT);
		xFingerprint.setTimestamp(new Timestamp(System.currentTimeMillis()));
		String[] params =
			{
				"lijstposities",
				KOAEncryptionUtil.fingerprintValueToString(baFingerprint)};
		String sMessage =
			this.getMessage(
				ErrorConstants.FINGERPRINT_KIESLIJST_CREATE_SINGLE_FINGERPRINT,
				params);
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.FINGERPRINT,
			"KiesLijst.saveFingerprint",
			"Systeem",
			sMessage);
		/* return xFingerprint */
		return xFingerprint;
	}
	/**
	 * Creates the current fingerprint of the kieslijsten of the kieslijst
	 * 
	 * @return Fingerprint fingerprint object with the current fingerprint, time and type
	 * 
	 * @throws KOAException Exception when something goes wrong during creation.
	 * 
	 */
	private Fingerprint createCurrentKieslijstFingerprint() throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesLijstBean.createCurrentKandidaatCodesFingerprint] Start creating fingerprints for kieslijsten...");
		/* init variables */
		Fingerprint xFingerprint = null;
		String sDataSource =
			JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA);
		/* create the fingerprint */
		byte[] baFingerprint =
			KOAEncryptionUtil.getFingerPrint(
				sDataSource,
				TechnicalProps.KIESLIJST_SCHEMA_NAME,
				TechnicalProps.KIESLIJST_KIESLIJST_TABLE_NAME,
				TechnicalProps.KIESLIJST_KIESLIJST_COLUMNS,
				TechnicalProps.KIESLIJST_KIESLIJST_SORT_KEY);
		/* fill up the object */
		xFingerprint = new Fingerprint();
		xFingerprint.setFingerprint(baFingerprint);
		xFingerprint.setFingerprintType(
			Fingerprint.KIESLIJST_KIESLIJSTEN_FINGERPRINT);
		xFingerprint.setTimestamp(new Timestamp(System.currentTimeMillis()));
		String[] params =
			{
				"kieslijsten",
				KOAEncryptionUtil.fingerprintValueToString(baFingerprint)};
		String sMessage =
			this.getMessage(
				ErrorConstants.FINGERPRINT_KIESLIJST_CREATE_SINGLE_FINGERPRINT,
				params);
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.FINGERPRINT,
			"KiesLijst.saveFingerprint",
			"Systeem",
			sMessage);
		/* return xFingerprint */
		return xFingerprint;
	}
	private String getMessage(String sCode, String[] params)
	{
		String sMessage = "";
		try
		{
			ErrorMessageFactory factory =
				ErrorMessageFactory.getErrorMessageFactory();
			sMessage = factory.getErrorMessage(sCode, params);
		}
		catch (java.io.IOException ioe)
		{
			String[] errorParams = { "Errormessage factory" };
			KOALogHelper.logErrorCode(
				"KiesLijstBean.getMessage",
				ErrorConstants.ERR_IO,
				errorParams,
				ioe);
			sMessage = "Fout bij laden melding";
		}
		return sMessage;
	}
}