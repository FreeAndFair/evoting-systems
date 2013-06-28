/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.esb.beans.ESBSessionEJBBean
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
  *  0.1		14-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.esb.beans;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.security.PrivateKey;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.Statement;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.Hashtable;
import java.util.Locale;
import java.util.StringTokenizer;
import java.util.Vector;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.rmi.PortableRemoteObject;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.apache.xalan.serialize.DOMSerializer;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

import com.logica.eplatform.error.ErrorMessageFactory;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.constants.VoteConstants;
import com.logicacmg.koa.dataobjects.CallResult;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.dataobjects.DecryptedStem;
import com.logicacmg.koa.dataobjects.EncryptedStem;
import com.logicacmg.koa.dataobjects.Fingerprint;
import com.logicacmg.koa.dataobjects.Kandidaat;
import com.logicacmg.koa.db.BLOBResultSet;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.esb.beans.ESBDecryptHelper;
import com.logicacmg.koa.esb.beans.ESBDecryptHelperHome;
import com.logicacmg.koa.esb.beans.ESBSequencesEJB;
import com.logicacmg.koa.esb.beans.ESBSequencesEJBHome;
import com.logicacmg.koa.esb.beans.ESBSequencesEJBKey;
import com.logicacmg.koa.esb.beans.Encryptedesb;
import com.logicacmg.koa.esb.beans.EncryptedesbHome;
import com.logicacmg.koa.esb.beans.Esbfingerprints;
import com.logicacmg.koa.esb.beans.EsbfingerprintsHome;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.koaschema.KieskringenKey;
import com.logicacmg.koa.koaschema.KieslijstenKey;
import com.logicacmg.koa.koaschema.Lijstposities;
import com.logicacmg.koa.koaschema.LijstpositiesHome;
import com.logicacmg.koa.koaschema.LijstpositiesKey;
import com.logicacmg.koa.security.KOAEncryptionUtil;
import com.logicacmg.koa.security.RandomGenerator;
import com.logicacmg.koa.utils.Convertor;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: KOAESBSessionEJB
 */
public class ESBSessionEJBBean implements javax.ejb.SessionBean
{
	//Constants used in methode telStemmen()
	private final static String KANDIDAATCODES_SELECT_SQL =
		"SELECT kc.kieskringnummer, kk.kieskringnaam, kc.kieslijstnummer, kc.positienummer, kl.lijstnaam FROM koa01.kandidaatcodes kc, koa01.kieslijsten kl, koa01.kieskringen kk WHERE kc.kieskringnummer = kl.kieskringnummer AND kc.kieskringnummer = kk.kieskringnummer AND kc.kieslijstnummer = kl.kieslijstnummer  GROUP BY kc.kieskringnummer, kk.kieskringnaam, kc.kieslijstnummer, kc.positienummer, kl.lijstnaam ORDER BY cast(kc.kieskringnummer as bigint), cast(kc.kieslijstnummer as bigint), cast(kc.positienummer as bigint)";
	private final static String AANTAL_KIESGERECHTIGDEN_SELECT_SQL =
		"SELECT count(stemcode) FROM koa01.kiezers WHERE verwijderd!='Y'";
	private final static String AANTAL_GESTEMDE_KIEZERS_SELECT_SQL =
		"SELECT count(stemnummer) FROM koa01.encryptedesb";
	private final static String AANTAL_NIET_GESTEMDE_KIEZERS_SELECT_SQL =
		"SELECT count(stemcode) FROM koa01.kiezers WHERE reedsgestemd!='Y' and verwijderd!='Y'";
	private final static String NUMBER_OF_VOTES_PER_KIESLIJST_SQL =
		"SELECT count(stemnummer) AS KIESLIJST_COUNT FROM koa01.decryptedesb WHERE kieskringnummer = ? AND kieslijstnummer = ?";
	private final static String KANDIDAAT_VOTE_COUNT_SQL =
		"SELECT count(stemnummer) AS KANDIDAAT_COUNT FROM koa01.decryptedesb WHERE kieskringnummer = ? AND kieslijstnummer = ? AND positienummer = ?";
	// constant used to get the starttime and endtime of the election
	public final static String TIME_OF_ELECTION_SELECT_SQL =
		"select timestamp from koa01.audit_log where action='STATE_CHANGE' AND upper(message) = ? order by timestamp";
	//constants used to store the report in telStemmen();
	public final static String REPORT_TYPE_ELECTION_RESULT =
		"VERKIEZINGSUITSLAG";
	public final static String REPORT_TYPE_DECRYPTED_VOTES = "DECRYPTED_VOTES";
	private final static String INSERT_REPORT_SQL =
		"INSERT INTO koa01.reports (id, type, timestamp, report) values (?,?,?,?)";
	private final static String NEW_REPORTS_ID_SQL =
		"SELECT max(id) + 1 AS NEW_ID FROM koa01.reports";
	private javax.ejb.SessionContext mySessionCtx;
	private final static String ESBFINGERPRINTS_TABLENAME = "ESBFINGERPRINTS";
	//used for creating fingerprint
	private final static String SCHEMA_NAME = "KOA01";
	private final static String TABLE_NAME = "ENCRYPTEDESB";
	private final static String[] COLUMNS = { "STEMNUMMER", "STEM" };
	private final static String SORT_KEY = "STEMNUMMER";
	//constant used for emtyESB
	private final static String EMPTY_ENCRYPTED_ESB_SQL =
		"DELETE FROM koa01.encryptedesb";
	private final static String EMPTY_DECRYPTED_ESB_SQL =
		"DELETE FROM koa01.decryptedesb";
	private final static String EMPTY_ESB_FINGERPRINT_SQL =
		"DELETE FROM koa01.esbfingerprints";
	private final static String IS_UNIQUE_ENCRYPTED_SQL =
		"SELECT COUNT(*) AS KEYCOUNT FROM KOA01.ENCRYPTEDESB WHERE STEMNUMMER = ?";
	private final static String IS_UNIQUE_DECRYPTED_SQL =
		"SELECT COUNT(*) AS KEYCOUNT FROM KOA01.DECRYPTEDESB WHERE STEMNUMMER = ?";
	//constants that contains the SQL to select all encrypted votes
	private final static String SELECT_ALL_ENCRYPTED_VOTES =
		"SELECT * FROM KOA01.ENCRYPTEDESB ORDER BY STEMNUMMER";
	private final static String DECRYPTED_VOTE_COUNT_SQL =
		"SELECT COUNT(*) AS ESB_COUNT FROM KOA01.DECRYPTEDESB";
	private final static String ENCRYPTED_VOTE_COUNT_SQL =
		"SELECT COUNT(*) AS ESB_COUNT FROM KOA01.ENCRYPTEDESB";
	//strings for auditing
	private final static String AUDIT_MESSAGE_FINGERPRINT_ERR =
		"Vingerafdrukken zijn niet gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_OK =
		"Vingerafdrukken zijn gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_CREATE =
		"Vingerafdruk van de ESB is aangemaakt met waarde: ";
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
	 * This method decrypts the data in the ESB and places the decrypted result 
	 * in a other table.
	 * 
	 * @param xPrivateKey The private key of the chairmn to encrypt the data.
	 * @param sPassword The password used to encrypt the private key
	 */
	public void openESB(byte[] baPrivateKey, String sPassword)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[ESBSessionEJBBean] entered openESB()");
		if (baPrivateKey.length == 0)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ESBSessionEJBBean] no private key provided");
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		Convertor xConvertor = new Convertor();
		PrivateKey xPrivateKey =
			xConvertor.byteArrayToPrivateKey(baPrivateKey, sPassword);
		if (xPrivateKey == null)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[ESBSessionEJBBean] key == null");
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		// Performance: changed routine to store the decrypted votes in configurable batches
		//              using a helper ejb to make sure this doens't happen in one big tx.
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
		int voteCommit =
			Integer.parseInt(
				TechnicalProps.getProperty(
					TechnicalProps.DECRYPTEDVOTE_COMMIT));
		int stemnummerCount = 0;
		int voteCount = 0;
		Vector vVotes = new Vector();
		Connection xConn = null;
		Statement xStatement = null;
		DecryptedStem decryptedStem = null;
		BLOBResultSet xRs = null;
		try
		{
			String[] columns = { "STEMNUMMER", "STEM" };
			xRs =
				new BLOBResultSet(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB),
					"KOA01",
					"ENCRYPTEDESB",
					"STEMNUMMER",
					columns);
			// Get a reference to the esbdecrypthelper
			ESBDecryptHelperHome dHome =
				ObjectCache.getInstance().getESBDecryptHelperHome();
			ESBDecryptHelper helper = dHome.create();
			//move to the first record.
			if (xRs != null)
			{
				while (xRs.next())
				{
					//get encrypted record
					byte[] baEncryptedData = xRs.getBytes("stem");
					//decrypt record
					String sConcatenatedVote =
						KOAEncryptionUtil.decrypt(xPrivateKey, baEncryptedData);
					//splits string
					if (sConcatenatedVote != null)
					{
						decryptedStem = new DecryptedStem();
						/*
						 * We define the stringtokenizer to also return the field separators.
						 * This is needed in case lijstnaam is empty. The string will then consist of:
						 * kandidaatcode;achternaam;voorletters;positienummer;districtnummer;kieslijstnummer;;kieskringnummer
						 */
						StringTokenizer xST =
							new StringTokenizer(
								sConcatenatedVote,
								VoteConstants.VOTE_FIELD_SEPARATOR,
								true);
						/*
						 * First token is the kandidaatcode
						 */
						String sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setKandidaatCode("");
						}
						else
						{
							decryptedStem.setKandidaatCode(checkQuote(sToken));
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Second token is the achternaam
						 */
						sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setAchternaam("");
						}
						else
						{
							decryptedStem.setAchternaam(checkQuote(sToken));
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Third token is the voorletters
						 */
						sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setVoorletters("");
						}
						else
						{
							decryptedStem.setVoorletters(checkQuote(sToken));
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Fourth token is the positienumber
						 */
						sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setPositienummer("");
						}
						else
						{
							decryptedStem.setPositienummer(sToken);
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Fifth token is the districtnumber
						 */
						sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setDistrictnummer("");
						}
						else
						{
							decryptedStem.setDistrictnummer(sToken);
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Sixth token is the kieslijstnumber
						 */
						sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setKieslijstnummer("");
						}
						else
						{
							decryptedStem.setKieslijstnummer(sToken);
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Seventh token is the lijstnaam
						 */
						sToken = xST.nextToken();
						if (sToken.equals(VoteConstants.VOTE_FIELD_SEPARATOR)
							== true)
						{
							decryptedStem.setLijstnaam("");
						}
						else
						{
							decryptedStem.setLijstnaam(checkQuote(sToken));
							// A VoteConstants.VOTE_FIELD_SEPARATOR
							sToken = xST.nextToken();
						}
						/*
						 * Eight token is the kieskringnummer
						 */
						sToken = xST.nextToken();
						if (sToken == null)
						{
							decryptedStem.setKieskringnummer("");
						}
						else
						{
							decryptedStem.setKieskringnummer(sToken);
						}
						vVotes.add(decryptedStem);
						voteCount++;
						if (voteCount == voteCommit)
						{
							stemnummerCount =
								helper.saveDecryptedVotes(
									vVotes,
									stemnummerCount);
							vVotes.clear();
							voteCount = 0;
						}
					} //if
				} //while
				if (voteCount < voteCommit)
				{
					stemnummerCount =
						helper.saveDecryptedVotes(vVotes, stemnummerCount);
				}
				xRs.close();
			} //if
		} //try
		catch (CreateException xCreateException)
		{
			String[] params = { "ESBDecryptHelperHome" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_CREATE,
				params,
				xCreateException);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (RemoteException xRemoteException)
		{
			String[] params = { "ESBDecryptHelperHome" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteException);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		finally
		{
			xRs.close();
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving openESB()");
	}
	/**
	 * Private method to return the string representation of the start time or end time of the election.
	 * 
	 * @param electionDate  The start/enddate of the election
	 * 
	 * @return String  		The string representation of the date
	 */
	private String convertTimeOfElectionToString(Timestamp tsElectionDate)
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] convertTimeOfElectionToString");
		// Convert the timestamp to the string representation
		SimpleDateFormat sdFormat =
			new SimpleDateFormat("dd-MMMM-yyyy HH:mm", new Locale("nl", "NL"));
		String sTijdStemming = sdFormat.format(tsElectionDate);
		return sTijdStemming;
	}
	/**
	 * This method counts the votes stored in the decrypted ESB table and places 
	 * the result in XML format in the reports table
	 * 
	 */
	public void telStemmen() throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] entered telStemmen()");
		/* variabeles for XML document */
		DocumentBuilder db = null;
		DocumentBuilderFactory factory = null;
		Document doc = null;
		/* blank candidate indicator */
		String blankVoteIndicator = null;
		String blankVoteLabel = null;
		String blankVoteReportHeader = null;
		try
		{
			/* create the XML document */
			factory = DocumentBuilderFactory.newInstance();
			db = (DocumentBuilder) factory.newDocumentBuilder();
			doc = db.newDocument();
			/* append the overall rootnode */
			Node rootNode = doc.createElement("verkiezingsuitslag");
			doc.appendChild(rootNode);
		}
		catch (Exception e)
		{
			KOALogHelper.logError(
				"ESBSessionEJBBean.telStemmen",
				"Exception while making new DocumentBuilder: " + e.getMessage(),
				e);
			throw new KOAException(ErrorConstants.ESB_TELSTEMMEN_ERR);
		}
		try
		{
			/* get blank candidate indicator from functional props */
			blankVoteIndicator =
				FunctionalProps.getProperty(
					FunctionalProps.BLANK_VOTE_INDICATOR);
			blankVoteLabel =
				FunctionalProps.getProperty(
					FunctionalProps.BLANK_VOTE_REPORT_LABEL);
			blankVoteReportHeader =
				FunctionalProps.getProperty(
					FunctionalProps.BLANK_VOTE_REPORT_HEADER);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"ESBSessionEJBBean.telStemmen",
				"Exception while getting blank candidate indicator: "
					+ koae.getMessage(),
				koae);
		}
		try
		{
			String sKiesGerechtig = "";
			String sAantalGestemdeKiezers = "";
			String sAantalNietGestemdeKiezers = "";
			String sStarttijdStemming = "";
			String sEindtijdStemming = "";
			Timestamp tsBeginStemming = null;
			Timestamp tsEindStemming = null;
			DBUtils xKOADBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
			DBUtils xESBDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
			DBUtils xKRDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR));
			Connection xKOAConn = xKOADBUtils.getConnection();
			Connection xESBConn = xESBDBUtils.getConnection();
			Connection xKRConn = xKRDBUtils.getConnection();
			//get kandidaten
			Statement xStatement = xKOAConn.createStatement();
			ResultSet xKandidatenRS =
				xKOADBUtils.executeResultQuery(
					xStatement,
					KANDIDAATCODES_SELECT_SQL);
			//get aantal kiesgerechtigden
			Statement xKiesGerechtigStatement = xKRConn.createStatement();
			ResultSet xKiesGerechtigRS =
				xKOADBUtils.executeResultQuery(
					xKiesGerechtigStatement,
					AANTAL_KIESGERECHTIGDEN_SELECT_SQL);
			if ((xKandidatenRS != null) && (xKiesGerechtigRS.next()))
			{
				sKiesGerechtig = xKiesGerechtigRS.getString(1);
			}
			xKiesGerechtigRS.close();
			xKiesGerechtigStatement.close();
			//get aantal gestemde kiezers
			Statement xAantalGestemdeKiezersStatement =
				xESBConn.createStatement();
			ResultSet xAantalGEstemdeKiezersRS =
				xKOADBUtils.executeResultQuery(
					xAantalGestemdeKiezersStatement,
					AANTAL_GESTEMDE_KIEZERS_SELECT_SQL);
			if ((xAantalGEstemdeKiezersRS != null)
				&& (xAantalGEstemdeKiezersRS.next()))
			{
				sAantalGestemdeKiezers = xAantalGEstemdeKiezersRS.getString(1);
			}
			xAantalGEstemdeKiezersRS.close();
			xAantalGestemdeKiezersStatement.close();
			//get aantal niet gestemde kiezers
			Statement xAantalNietGestemdeKiezersStatement =
				xKRConn.createStatement();
			ResultSet xAantalNietGEstemdeKiezersRS =
				xKOADBUtils.executeResultQuery(
					xAantalNietGestemdeKiezersStatement,
					AANTAL_NIET_GESTEMDE_KIEZERS_SELECT_SQL);
			if ((xAantalNietGEstemdeKiezersRS != null)
				&& (xAantalNietGEstemdeKiezersRS.next()))
			{
				sAantalNietGestemdeKiezers =
					xAantalNietGEstemdeKiezersRS.getString(1);
			}
			xAantalNietGEstemdeKiezersRS.close();
			xAantalNietGestemdeKiezersStatement.close();
			//get starttijd van de stemming uit de auditlog
			String[] openParam = { "Open" };
			String sOpenStemming =
				getMessage(
					ErrorConstants.CHANGE_STATE_AUDIT_SAVE_STATE,
					openParam)
					.toUpperCase();
			PreparedStatement xStarttijdStemmingPrepStatement =
				xKOAConn.prepareStatement(TIME_OF_ELECTION_SELECT_SQL);
			xStarttijdStemmingPrepStatement.setString(1, sOpenStemming);
			ResultSet xStarttijdStemmingRS =
				xStarttijdStemmingPrepStatement.executeQuery();
			if (xStarttijdStemmingRS != null)
			{
				if (xStarttijdStemmingRS.next())
				{
					tsBeginStemming = xStarttijdStemmingRS.getTimestamp(1);
					// Convert the Timestamp to the string with dateformat dd-MMMM-yyyy HH:mm
					sStarttijdStemming =
						convertTimeOfElectionToString(tsBeginStemming);
				}
			}
			//get eindtijd van de stemming uit de auditlog
			String[] closeParam = { "Gesloten" };
			String sClosedStemming =
				getMessage(
					ErrorConstants.CHANGE_STATE_AUDIT_SAVE_STATE,
					closeParam)
					.toUpperCase();
			PreparedStatement xEindtijdStemmingPrepStatement =
				xKOAConn.prepareStatement(TIME_OF_ELECTION_SELECT_SQL);
			xEindtijdStemmingPrepStatement.setString(1, sClosedStemming);
			ResultSet xEindtijdStemmingRS =
				xEindtijdStemmingPrepStatement.executeQuery();
			if (xEindtijdStemmingRS != null)
			{
				if (xEindtijdStemmingRS.next())
				{
					tsEindStemming = xEindtijdStemmingRS.getTimestamp(1);
					// Convert the Timestamp to the string with dateformat dd-MMMM-yyyy HH:mm
					sEindtijdStemming =
						convertTimeOfElectionToString(tsEindStemming);
				}
			}
			//move to the first record.
			if (xKandidatenRS != null)
			{
				Element nKiesKring = null;
				Element nKiesLijst = null;
				Element nKandidaat = null;
				String sKieskringnummer = "";
				String sKieslijstnummer = "";
				String sKieskringnaam = "";
				while (xKandidatenRS.next())
				{
					String sPositienummer =
						xKandidatenRS.getString("positienummer");
					int iKieslijstCount = 0;
					if (!sKieskringnummer
						.equals(xKandidatenRS.getString("kieskringnummer")))
					{
						sKieskringnummer =
							xKandidatenRS.getString("kieskringnummer");
						sKieskringnaam =
							xKandidatenRS.getString("kieskringnaam");
						//
						nKiesKring = doc.createElement("kieskring");
						doc.getDocumentElement().appendChild(nKiesKring);
						nKiesKring.setAttribute("ID", sKieskringnummer);
						nKiesKring.setAttribute("Kieskring", sKieskringnaam);
						nKiesKring.setAttribute(
							"Stembureau",
							FunctionalProps.getProperty(
								FunctionalProps.VOTING_OFFICE));
						nKiesKring.setAttribute(
							"Verkiezing",
							FunctionalProps.getProperty(
								FunctionalProps.ELECTION_DESCRIPTION));
						nKiesKring.setAttribute(
							"StarttijdStemming",
							sStarttijdStemming);
						nKiesKring.setAttribute(
							"EindtijdStemming",
							sEindtijdStemming);
						nKiesKring.setAttribute(
							"KiesGerechtigden",
							sKiesGerechtig);
						nKiesKring.setAttribute(
							"StartDatumTijd",
							FunctionalProps.getProperty(
								FunctionalProps.VOTING_START_DATE_TIME));
						nKiesKring.setAttribute(
							"StopDatumTijd",
							FunctionalProps.getProperty(
								FunctionalProps.VOTING_END_DATE_TIME));
						nKiesKring.setAttribute(
							"AantalGestemdeKiezers",
							sAantalGestemdeKiezers);
						nKiesKring.setAttribute(
							"AantalNietGestemdeKiezers",
							sAantalNietGestemdeKiezers);
					}
					if (!sKieslijstnummer
						.equals(xKandidatenRS.getString("kieslijstnummer")))
					{
						sKieslijstnummer =
							xKandidatenRS.getString("kieslijstnummer");
						String sKieslijstNaam =
							xKandidatenRS.getString("lijstnaam");
						;
						nKiesLijst = doc.createElement("kieslijst");
						nKiesKring.appendChild(nKiesLijst);
						/* Check whether lijstnaam equals blank vote indicator */
						if (blankVoteIndicator != null
							&& blankVoteIndicator.equals(sKieslijstNaam))
						{
							nKiesLijst.setAttribute("KiesLijstNummer", null);
							nKiesLijst.setAttribute(
								"lijstnaam",
								blankVoteReportHeader);
						}
						else
						{
							nKiesLijst.setAttribute(
								"KiesLijstNummer",
								sKieslijstnummer);
							nKiesLijst.setAttribute(
								"lijstnaam",
								sKieslijstNaam);
						}
						//get number of votes per kieslijst (partij)
						PreparedStatement xPrepStatement =
							xESBConn.prepareStatement(
								NUMBER_OF_VOTES_PER_KIESLIJST_SQL);
						xPrepStatement.setString(1, sKieskringnummer);
						//kieskringnummer
						xPrepStatement.setString(2, sKieslijstnummer);
						//kieslijstnummer
						ResultSet xKieslijstCount =
							xPrepStatement.executeQuery();
						if (xKieslijstCount != null)
						{
							if (xKieslijstCount.next())
							{
								iKieslijstCount =
									xKieslijstCount.getInt("KIESLIJST_COUNT");
							}
							xKieslijstCount.close();
						}
						nKiesLijst.setAttribute(
							"totaal_stemmen",
							Integer.toString(iKieslijstCount));
						xPrepStatement.close();
					}
					//get kandidaat info
					Kandidaat xKandidaat =
						getKandidaatByLijstpositie(
							sKieskringnummer,
							sKieslijstnummer,
							sPositienummer);
					if (xKandidaat != null)
					{
						//count number of votes per kandidaat		  
						PreparedStatement xPrepStatement =
							xESBConn.prepareStatement(KANDIDAAT_VOTE_COUNT_SQL);
						xPrepStatement.setString(1, sKieskringnummer);
						//kieskringnummer
						xPrepStatement.setString(2, sKieslijstnummer);
						//kieslijstnummer
						xPrepStatement.setString(3, sPositienummer);
						//kieslijstnummer
						ResultSet xKandidaatCount =
							xPrepStatement.executeQuery();
						int iKandidaatCount = 0;
						if (xKandidaatCount != null)
						{
							if (xKandidaatCount.next())
							{
								iKandidaatCount =
									xKandidaatCount.getInt("KANDIDAAT_COUNT");
							}
							xKandidaatCount.close();
						}
						nKandidaat = doc.createElement("kandidaat");
						nKiesLijst.appendChild(nKandidaat);
						if (blankVoteIndicator != null
							&& blankVoteIndicator.equals(xKandidaat.achterNaam))
						{
							nKandidaat.setAttribute(
								"achternaam",
								blankVoteLabel);
							nKandidaat.setAttribute("voorletters", "");
							nKandidaat.setAttribute(
								"lijstpositie",
								xKandidaat.positienummer);
							nKandidaat.setAttribute(
								"aantalstemmen",
								Integer.toString(iKandidaatCount));
						}
						else
						{
							nKandidaat.setAttribute(
								"achternaam",
								xKandidaat.achterNaam);
							nKandidaat.setAttribute(
								"voorletters",
								xKandidaat.voorletters);
							nKandidaat.setAttribute(
								"lijstpositie",
								xKandidaat.positienummer);
							nKandidaat.setAttribute(
								"aantalstemmen",
								Integer.toString(iKandidaatCount));
						}
						xPrepStatement.close();
					}
				} //while
				xKandidatenRS.close();
			} //if
			String sEncoding = "UTF-8";
			try
			{
				sEncoding =
					TechnicalProps.getProperty(TechnicalProps.XML_ENCODING);
			}
			catch (KOAException koae)
			{
				KOALogHelper.logError(
					"ESBSessionEJBBean.telStemmen",
					"Could not find the XML encoding property in the technical properties, using default UTF-8",
					koae);
			}
			/* opslaan van de xml in de database */
			ByteArrayOutputStream os = new ByteArrayOutputStream();
			DOMSerializer ds =
				new XMLSerializer(os, new OutputFormat("XML", sEncoding, true))
					.asDOMSerializer();
			ds.serialize(doc);
			/* get the XML from the outputstream */
			byte[] bArray = os.toByteArray();
			InputStream bis = new ByteArrayInputStream(bArray);
			/* store the XML */
			ResultSet xRsNewID =
				xKOADBUtils.executeResultQuery(
					xKOAConn.createStatement(),
					NEW_REPORTS_ID_SQL);
			if (xRsNewID != null)
			{
				if (xRsNewID.next())
				{
					//insert record into reports table
					BigDecimal xNewID = xRsNewID.getBigDecimal("NEW_ID");
					PreparedStatement xPrepStatement =
						xKOAConn.prepareStatement(INSERT_REPORT_SQL);
					xPrepStatement.setBigDecimal(1, xNewID); //id
					xPrepStatement.setString(
						2,
						this.REPORT_TYPE_ELECTION_RESULT);
					//type
					xPrepStatement.setTimestamp(
						3,
						new java.sql.Timestamp(System.currentTimeMillis()));
					//timestamp
					xPrepStatement.setBinaryStream(4, bis, bArray.length);
					xPrepStatement.executeUpdate();
				}
				xRsNewID.close();
			}
			xKandidatenRS.close();
			xStatement.close();
			xKOAConn.close();
			xESBConn.close();
			xKRConn.close();
		} //try
		catch (java.sql.SQLException xSQLExc)
		{
			String[] params = { "Count votes" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_SQL,
				params,
				xSQLExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (java.io.IOException xIOExc)
		{
			String[] params = { "byte array output stream" };
			KOALogHelper.logErrorCode(
				"[ESBSessionEJBBean]",
				ErrorConstants.ERR_IO,
				params,
				xIOExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving telStemmen()");
	}
	/**
	 * This method initializes the ESB
	 * 
	 * @return CallREsult object that contains the result of the initialisation.
	 * 
	 */
	private CallResult initialize()
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] entered initialize()");
		CallResult xCallResult = new CallResult();
		//set default value
		xCallResult.setResult(CallResult.RESULT_OK);
		//check if the ESB is empty
		if (getVoteCount() != 0 || getVoteCountDecryptedESB() != 0)
		{
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.STATE_CHANGE,
				ComponentType.ESB,
				getSessionContext().getCallerPrincipal().getName(),
				this.getMessage(
					ErrorConstants.CHANGE_STATE_AUDIT_ESB_NOT_EMPTY,
					null));
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[ESBSessionEJBBean] ESB not empty");
			xCallResult.setResult(CallResult.ESB_NOT_EMPTY);
		}
		else
		{
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.STATE_CHANGE,
				ComponentType.ESB,
				getSessionContext().getCallerPrincipal().getName(),
				this.getMessage(
					ErrorConstants.CHANGE_STATE_AUDIT_ESB_EMPTY,
					null));
		}
		//initialize the counters
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving initialize()");
		return xCallResult;
	}
	/**
	 *  This method performs actions when the system state is going to be changed.
	 * 
	 *  Note: The system isn't in the new state yet, this method performs the actions needed
	 *        for the transition to the new state! 
	 * 
	 * @param sCurrentState The current state the system is in
	 * @param sNewState String Indication of the new system state. 
	 *                         (The value comes from the SystemState class)
	 * 
	 */
	public void changeState(String sCurrentState, String sNewState)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] entered changeState()");
		CallResult xCallResult = new CallResult();
		xCallResult.setResult(CallResult.RESULT_OK);
		if (sNewState.equals(SystemState.INITIALIZED))
		{
			xCallResult = initialize();
		}
		else if (sNewState.equals(SystemState.SUSPENDED))
		{
			xCallResult = checkESB(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.CLOSED))
		{
			xCallResult = checkESB(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.RE_INITIALIZED))
		{
			xCallResult = checkESB(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.READY_TO_COUNT))
		{
			xCallResult = checkESB(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.BLOCKED))
		{
			xCallResult = block();
		}
		else if (sNewState.equals(SystemState.VOTES_COUNTED))
		{
			//nothing to do
		}
		else if (sNewState.equals(SystemState.OPEN))
		{
			//nothing to do
		}
		else if (sNewState.equals(SystemState.PREPARE))
		{
			//nothing to do
		}
		else
		{
			xCallResult.setResult(CallResult.RESULT_UNKNOWN);
		}
		if (xCallResult.getResult() == CallResult.FINGERPRINT_ESB_ERR)
		{
			throw new KOAException(ErrorConstants.ESB_FINGERPRINT_ERROR);
		}
		if (xCallResult.getResult() == CallResult.ESB_NOT_EMPTY)
		{
			throw new KOAException(ErrorConstants.ESB_NOT_EMPTY_DURING_INIT);
		}
		if (xCallResult.getResult() != CallResult.RESULT_OK)
		{
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving changeState()");
	} //changeState
	/**
	 * This method handles the actions that have to be performed for the ESB component when the 
	 * system transits to one of te following states:
	 * SUSPENDED
	 * CLOSED
	 * REINITIALIZED
	 * READY_TO_COUNT
	 *      
	 * @param sNewState The new system state.
	 * 
	 * @return CallResult object 
	 * 
	 */
	private CallResult checkESB(String sCurrentState, String sNewState)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] entered checkESB()");
		boolean bFingerprintsChecked = false;
		Fingerprint xNewFingerprint = null, xLastStoredFingerprint = null;
		CallResult xCallResult = new CallResult();
		//set default value
		xCallResult.setResult(CallResult.RESULT_OK);
		if (sNewState.equals(SystemState.SUSPENDED)
			|| sNewState.equals(SystemState.CLOSED)
			|| sNewState.equals(SystemState.RE_INITIALIZED)
			|| sNewState.equals(SystemState.READY_TO_COUNT))
		{
			//create a new fingerprint
			xNewFingerprint = createFingerprint();
			String sFingerprintMessage =
				AUDIT_MESSAGE_FINGERPRINT_CREATE
					+ KOAEncryptionUtil.fingerprintValueToString(
						xNewFingerprint.getFingerprint());
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.ESB,
				getSessionContext().getCallerPrincipal().getName(),
				sFingerprintMessage);
		}
		if (sNewState.equals(SystemState.RE_INITIALIZED)
			|| sNewState.equals(SystemState.READY_TO_COUNT)
			|| (sNewState.equals(SystemState.CLOSED)
				&& sCurrentState.equals(SystemState.SUSPENDED)))
		{
			//get the last stored fingerprint 
			xLastStoredFingerprint = getLastStoredFingerprint();
			/*
			 * compare the new created fingerprints with the ones that are created 
			 * during the initialize state.
			 */
			if (xLastStoredFingerprint == null
				|| !xLastStoredFingerprint.equals(xNewFingerprint))
			{
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[ESBSessionEJBBean] ESB Fingerprints aren't in sync");
				xCallResult.setResult(CallResult.FINGERPRINT_ESB_ERR);
			}
			bFingerprintsChecked = true;
		}
		//store esb fingerprint
		saveFingerprint(xNewFingerprint, sNewState);
		//log fingerprint to the audit table
		if (xCallResult.getResult() == CallResult.FINGERPRINT_ESB_ERR)
		{
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.ESB,
				getSessionContext().getCallerPrincipal().getName(),
				AUDIT_MESSAGE_FINGERPRINT_ERR);
		}
		else if (bFingerprintsChecked)
		{
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.ESB,
				getSessionContext().getCallerPrincipal().getName(),
				AUDIT_MESSAGE_FINGERPRINT_OK);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving checkESB() with value "
				+ xCallResult.getResult());
		return xCallResult;
	}
	/**
	 * This method handles te actions that have to be performed for the KR component
	 * when the system transits to the blocked state.
	 * 
	 * @return CallResult object 
	 * 
	 */
	private CallResult block() throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.WARNING,
			"[ESBSessionEJBBean] entered block()");
		CallResult xCallResult = new CallResult();
		//set default value
		xCallResult.setResult(CallResult.RESULT_OK);
		getVoteCount();
		return xCallResult;
	}
	/**
	 * This method retrieves the latest stored fingerprint for the esb.
	 * 
	 * @return Esbfingerprints entity bean.
	 */
	private Esbfingerprints getLatestFingerprintesbEJB()
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] entered getLatestFingerprintesbEJB()");
		Esbfingerprints xEsbfingerprints = null;
		try
		{
			EsbfingerprintsHome xEsbfingerprintsHome =
				ObjectCache.getInstance().getESBFingerprintsHome();
			xEsbfingerprints = xEsbfingerprintsHome.findLatestFingerprint();
		}
		catch (javax.ejb.FinderException xFinderExc)
		{
			String[] params = { "Esbfingerprints" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderExc);
			xEsbfingerprints = null;
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Esbfingerprints" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving getLatestFingerprintesbEJB()");
		return xEsbfingerprints;
	}
	/**
	 *
	 * Retrieves the last stored fingerprint.
	 * 
	 * @return Fingerprint data object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Fingerprint getLastStoredFingerprint()
		throws com.logicacmg.koa.exception.KOAException
	{
		Fingerprint xLastStoredFingerprint = null;
		try
		{
			Esbfingerprints xEsbfingerprints = getLatestFingerprintesbEJB();
			if (xEsbfingerprints != null)
			{
				xLastStoredFingerprint = new Fingerprint();
				xLastStoredFingerprint.setFingerprint(
					xEsbfingerprints.getFingerprint());
				xLastStoredFingerprint.setFingerprintType(
					Fingerprint.ESB_FINGERPRINT);
			}
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Fingerprint" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		return xLastStoredFingerprint;
	}
	/**
	 * counts the number of votes in the encrypted ESB.
	 * 
	 * @return int - The number of votes in the encrypted esb
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getVoteCount() throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] Entering getVoteCount()");
		int iVoteCount = -1;
		try
		{
			DBUtils xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
			Connection xConn = xDBUtils.getConnection();
			Statement xStatement = xConn.createStatement();
			ResultSet xRs =
				xDBUtils.executeResultQuery(
					xStatement,
					ENCRYPTED_VOTE_COUNT_SQL);
			//move to the first record.
			if (xRs != null && xRs.next())
			{
				iVoteCount = xRs.getInt("ESB_COUNT");
				xDBUtils.closeResultSet(xRs);
				xDBUtils.closeStatement(xStatement);
				xDBUtils.closeConnection(xDBUtils.getConnection());
			}
		}
		catch (java.sql.SQLException xSQLExc)
		{
			String[] params = { "Get vote count" };
			KOALogHelper.logErrorCode(
				"[ESBSessionEJBBean]",
				ErrorConstants.ERR_SQL,
				params,
				xSQLExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving getVoteCount()");
		return iVoteCount;
	}
	/**
	 * counts the number of votes in the derypted ESB.
	 * 
	 * @return int - The number of votes in the decrypted esb
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getVoteCountDecryptedESB()
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] Entering getVoteCountDecryptedESB()");
		int iVoteCount = -1;
		try
		{
			DBUtils xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
			Connection xConn = xDBUtils.getConnection();
			Statement xStatement = xConn.createStatement();
			ResultSet xRs =
				xDBUtils.executeResultQuery(
					xStatement,
					DECRYPTED_VOTE_COUNT_SQL);
			//move to the first record.
			if (xRs != null && xRs.next())
			{
				iVoteCount = xRs.getInt("ESB_COUNT");
				xDBUtils.closeResultSet(xRs);
				xDBUtils.closeStatement(xStatement);
				xDBUtils.closeConnection(xDBUtils.getConnection());
			}
		}
		catch (java.sql.SQLException xSQLExc)
		{
			String[] params = { "Get vote count decrypted ESB" };
			KOALogHelper.logErrorCode(
				"[ESBSessionEJBBean]",
				ErrorConstants.ERR_SQL,
				params,
				xSQLExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] leaving getVoteCountDecryptedESB()");
		return iVoteCount;
	}
	/**
	 * creates a new fingerprint for the esb
	 * 
	 * @return Fingerprint data object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Fingerprint createFingerprint()
		throws com.logicacmg.koa.exception.KOAException
	{
		com.logicacmg.koa.dataobjects.Fingerprint xNewFP =
			new com.logicacmg.koa.dataobjects.Fingerprint();
		xNewFP.setFingerprint(
			KOAEncryptionUtil.getBLOBFingerPrint(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB),
				SCHEMA_NAME,
				TABLE_NAME,
				COLUMNS,
				SORT_KEY));
		xNewFP.setFingerprintType(Fingerprint.ESB_FINGERPRINT);
		xNewFP.setTimestamp(new java.sql.Timestamp(System.currentTimeMillis()));
		return xNewFP;
	}
	/**
	 * Stores a fingeprint
	 * 
	 * @param Fingerprint - The fingeprint to be stored
	 * @param sState - The state under which the fingeprint was created
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private void saveFingerprint(Fingerprint xFingerprint, String sState)
		throws com.logicacmg.koa.exception.KOAException
	{
		if (xFingerprint == null)
		{
			return;
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[ESBSessionEJBBean] entered saveFingerprint()");
		Esbfingerprints xEsbfingerprints = null;
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.ESB_SESSION_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.ESB_SESSION_PROVIDER));
		try
		{
			//get new id
			BigDecimal xKey = getNewID();
			if (xKey != null)
			{
				//create new bean
				InitialContext jndiContext = new InitialContext(htProps);
				Object xRef =
					jndiContext.lookup(
						JNDIProperties.getProperty(
							JNDIProperties.ESB_FINGERPRINT_EJB));
				EsbfingerprintsHome xEsbfingerprintsHome =
					(EsbfingerprintsHome) PortableRemoteObject.narrow(
						xRef,
						EsbfingerprintsHome.class);
				xEsbfingerprints =
					xEsbfingerprintsHome.create(
						xKey,
						xFingerprint.getFingerprint(),
						xFingerprint.getTimestamp(),
						sState);
			}
		}
		catch (javax.naming.NamingException xNamingException)
		{
			String[] params = { "Esbfingerprints" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_NAMING,
				params,
				xNamingException);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Esbfingerprints" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (javax.ejb.CreateException xCreateExc)
		{
			String[] params = { "Esbfingerprints" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_CREATE,
				params,
				xCreateExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
	}
	/**
	 * Determines a new unique id.
	 * 
	 * @return BigDecimal - The new unique id
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private BigDecimal getNewID()
		throws com.logicacmg.koa.exception.KOAException
	{
		BigDecimal xNewID = null;
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.ESB_SESSION_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.ESB_SESSION_PROVIDER));
		try
		{
			InitialContext jndiContext = new InitialContext(htProps);
			Object xRef =
				jndiContext.lookup(
					JNDIProperties.getProperty(
						JNDIProperties.ESB_SEQUENCE_EJB));
			ESBSequencesEJBHome xESBSequencesEJBHome =
				(ESBSequencesEJBHome) PortableRemoteObject.narrow(
					xRef,
					ESBSequencesEJBHome.class);
			ESBSequencesEJB xESBSequencesEJB =
				xESBSequencesEJBHome.findByPrimaryKey(
					new ESBSequencesEJBKey(ESBFINGERPRINTS_TABLENAME));
			if (xESBSequencesEJB != null)
			{
				//retrieve the last generated id
				xNewID = xESBSequencesEJB.getNextID();
				if (xNewID != null)
				{
					//create new id
					xNewID = xNewID.add(new BigDecimal(1));
					//store the new id
					xESBSequencesEJB.setNextID(xNewID);
				}
			}
		}
		catch (javax.naming.NamingException xNamingException)
		{
			String[] params = { "ESBSequencesEJB" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_NAMING,
				params,
				xNamingException);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (javax.ejb.FinderException xFinderException)
		{
			String[] params =
				{
					"ESBSequencesEJB : ID for "
						+ ESBFINGERPRINTS_TABLENAME
						+ " IS NOT CONFIGURED" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderException);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "ESBSequencesEJB" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		return xNewID;
	}
	/**
	 * Collects the counters for the ESB.
	 * 
	 * @return CounterData object that contains the counters
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public CounterData collectCounters(String sComponentID)
		throws com.logicacmg.koa.exception.KOAException
	{
		CounterData xCounterData =
			new CounterData(ComponentType.ESB, sComponentID);
		xCounterData.setCounter(
			CounterKeys.STEMMEN_UITGEBRACHT,
			getVoteCount());
		return xCounterData;
	}
	/**
	 * Stores an encrypted vote
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public void saveEncryptedVote(EncryptedStem xEncryptedStem)
		throws com.logicacmg.koa.exception.KOAException
	{
		BigDecimal xStemnummer = null;
		boolean bUniqueFound = false;
		int iLoopCounter = 0;
		EncryptedesbHome xEncryptedesbHome =
			ObjectCache.getInstance().getEncryptedESBHome();
		Encryptedesb xEncryptedesb = null;
		int maxCreateAttempts =
			TechnicalProps.getIntProperty(TechnicalProps.MAX_RANDOM_ATTEMPTS);
		while (!bUniqueFound)
		{
			try
			{
				xStemnummer = RandomGenerator.getInstance().getRandomNumber(15);
				xEncryptedesb = xEncryptedesbHome.create(xStemnummer);
				bUniqueFound = true;
			}
			catch (javax.ejb.DuplicateKeyException de)
			{
				iLoopCounter++;
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[ESBSessionEJBBean] Duplicate key while trying to instert vote, attempt: "
						+ iLoopCounter
						+ " of "
						+ maxCreateAttempts);
				if (iLoopCounter > maxCreateAttempts)
				{
					KOALogHelper.log(
						KOALogHelper.ERROR,
						"ESBSessionEJBBean Unable to retrieve a new unique random key for encryptedesb");
					throw new KOAException(ErrorConstants.ESB_ERROR);
				}
				bUniqueFound = false;
			}
			catch (javax.ejb.CreateException xCreateExc)
			{
				String[] params = { "Encryptedesb" };
				KOALogHelper.logErrorCode(
					"[ESBSessionEJBBean]",
					ErrorConstants.ERR_CREATE,
					params,
					xCreateExc);
				throw new KOAException(ErrorConstants.ESB_ERROR);
			}
			catch (java.rmi.RemoteException xRemoteExc)
			{
				String[] params = { "Encryptedesb" };
				KOALogHelper.logErrorCode(
					"[ESBSessionEJBBean]",
					ErrorConstants.ERR_REMOTE,
					params,
					xRemoteExc);
				throw new KOAException(ErrorConstants.ESB_ERROR);
			}
			// end while
		}
		try
		{
			xEncryptedesb.setStem(xEncryptedStem.encryptedVote);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			KOALogHelper.log(KOALogHelper.TRACE, "Remote exception");
			String[] params = { "Encryptedesb" };
			KOALogHelper.logErrorCode(
				"[ESBSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
	}
	/**
	 * Retrieves a kandidaat by it's primary key
	 * 
	 * @return kandidaat data object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Kandidaat getKandidaatByLijstpositie(
		String sKieskringnummer,
		String sKieslijstnummer,
		String sPositienummer)
		throws com.logicacmg.koa.exception.KOAException
	{
		Kandidaat xKandidaat = null;
		try
		{
			LijstpositiesHome xLijstpositiesHome =
				ObjectCache.getInstance().getLijstpositiesHome();
			Lijstposities xLijstposities =
				xLijstpositiesHome.findByPrimaryKey(
					new LijstpositiesKey(
						sPositienummer,
						new KieslijstenKey(
							sKieslijstnummer,
							new KieskringenKey(sKieskringnummer))));
			xKandidaat = new Kandidaat();
			xKandidaat.achterNaam = xLijstposities.getAchternaam();
			xKandidaat.voorletters = xLijstposities.getVoorletters();
			xKandidaat.kieskringnummer = sKieskringnummer;
			xKandidaat.kieslijstnummer = sKieslijstnummer;
			xKandidaat.positienummer = sPositienummer;
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Lijstposities" };
			KOALogHelper.logErrorCode(
				"[ESBSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		catch (javax.ejb.FinderException xFinderExc)
		{
			xKandidaat = null;
		}
		return xKandidaat;
	}
	/**
	 * Deletes all entries in the tables: encryptedesb, decryptedesb and esbfingerprints
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public void emptyESB() throws com.logicacmg.koa.exception.KOAException
	{
		try
		{
			DBUtils xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
			//empty the encrypted esb
			if (xDBUtils.executeQuery(EMPTY_ENCRYPTED_ESB_SQL) < 1)
			{
				throw new KOAException(ErrorConstants.ESB_ERROR);
			}
			//empty the decrypted esb
			if (xDBUtils.executeQuery(EMPTY_DECRYPTED_ESB_SQL) < 1)
			{
				throw new KOAException(ErrorConstants.ESB_ERROR);
			}
			if (xDBUtils.executeQuery(EMPTY_ESB_FINGERPRINT_SQL) < 1)
			{
				throw new KOAException(ErrorConstants.ESB_ERROR);
			}
		}
		catch (com.logicacmg.koa.exception.KOADBException xKOADBExc)
		{
			KOALogHelper.logError("ESBSessionEJBBean", "", xKOADBExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
	}
	/**
	  * Checks if  a key for the encryptedesb table or decryptedesb table already exists or not
	  * 
	  * @param xKey - The number to be checked
	  * @param bEncryptedUniquenessCheck - Boolean that indicates if the encryptedesb or decryptedesb table has to be checked
	  * 
	  * @return True  - ID is unique (i.e.  it doesn't exists (yet))
	  *         False - ID already exists	 
	  * @exception com.logicacmg.koa.exception.KOAException
	  */
	private boolean isUnique(
		BigDecimal xKey,
		boolean bEncryptedUniquenessCheck)
		throws com.logicacmg.koa.exception.KOAException
	{
		PreparedStatement xPrepStatement = null;
		ResultSet xRs = null;
		Connection xConn = null;
		try
		{
			DBUtils xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
			xConn = xDBUtils.getConnection();
			if (bEncryptedUniquenessCheck)
			{
				xPrepStatement =
					xConn.prepareStatement(IS_UNIQUE_ENCRYPTED_SQL);
			}
			else
			{
				xPrepStatement =
					xConn.prepareStatement(IS_UNIQUE_DECRYPTED_SQL);
			}
			xPrepStatement.setBigDecimal(1, xKey);
			xRs = xPrepStatement.executeQuery();
			if (xRs != null)
			{
				if (xRs.next())
				{
					int iCount = xRs.getInt("KEYCOUNT");
					if (iCount > 0)
					{
						return false;
					}
				}
			}
			if (xRs != null)
			{
				xRs.close();
			}
			if (xPrepStatement != null)
			{
				xPrepStatement.close();
			}
			if (xConn != null)
			{
				xConn.close();
			}
		}
		catch (java.sql.SQLException xSQLExc)
		{
			String[] params = { "Is unique encrypted ESB" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_SQL,
				params,
				xSQLExc);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		return true;
	}
	/**
	  * Checks if a String contains a quote. If that's the case, is doubles the quote so it can be inserted into the DB.
	  * 
	  * @param sQuoteString - The string to be checked
	  * 
	  * @return String - The corrected string when the original string contained a quote else the original string is returned
	  * 
	  * @exception com.logicacmg.koa.exception.KOAException
	  */
	private String checkQuote(String sQuoteString)
	{
		final String QUOTE = "'";
		String sCorrectedString = "";
		int iPos = 0;
		int iLast = 0;
		int iPrevPos = 0;
		iLast = sQuoteString.lastIndexOf(QUOTE);
		if (iLast > -1)
		{
			while (iPos < iLast)
			{
				iPos = sQuoteString.indexOf(QUOTE, iPos);
				sCorrectedString =
					sCorrectedString
						+ sQuoteString.substring(iPrevPos, iPos)
						+ QUOTE;
				iPrevPos = iPos;
				iPos = iPos + 1;
			}
			if (iLast < sQuoteString.length())
			{
				sCorrectedString =
					sCorrectedString + sQuoteString.substring(iLast);
			}
		}
		else
		{
			return sQuoteString;
		}
		return sCorrectedString;
	}
	private String getMessage(String code, String[] params)
	{
		String sMessage = "";
		try
		{
			sMessage =
				ErrorMessageFactory.getErrorMessageFactory().getErrorMessage(
					code,
					params);
		}
		catch (java.io.IOException ioe)
		{
			String[] saParams = { "ErrorMessageFactory" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean.getMessage",
				ErrorConstants.ERR_IO,
				saParams,
				ioe);
			sMessage = "Kan melding met code " + code + " niet vinden.";
		}
		return sMessage;
	}
}