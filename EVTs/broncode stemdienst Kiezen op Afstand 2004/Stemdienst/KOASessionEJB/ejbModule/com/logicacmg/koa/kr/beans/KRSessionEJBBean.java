/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.kr.beans.KRSessionEJBBean
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
  *  0.1		11-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.kr.beans;
import java.math.BigDecimal;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.Statement;
import java.sql.Timestamp;

import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.CounterKeys;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.controller.beans.Koa_state;
import com.logicacmg.koa.dataobjects.CallResult;
import com.logicacmg.koa.dataobjects.CounterData;
import com.logicacmg.koa.dataobjects.Fingerprint;
import com.logicacmg.koa.dataobjects.Kiezer;
import com.logicacmg.koa.dataobjects.StemTransactie;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.kr.beans.KRFingerprints;
import com.logicacmg.koa.kr.beans.KRFingerprintsHome;
import com.logicacmg.koa.kr.beans.KRSequenceEJB;
import com.logicacmg.koa.kr.beans.KRSequenceEJBHome;
import com.logicacmg.koa.kr.beans.KRSequenceEJBKey;
import com.logicacmg.koa.kr.beans.Kiezers;
import com.logicacmg.koa.kr.beans.KiezersHome;
import com.logicacmg.koa.kr.beans.KiezersKey;
import com.logicacmg.koa.security.KOAEncryptionUtil;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
public class KRSessionEJBBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	private final static String KRSEQUENCE_TABLENAME = "KRFINGERPRINTS";
	//constants used to emtyp the kr
	private final static String EMPTY_KR_FINGERPRINT_SQL =
		"DELETE FROM KOA01.KRFINGERPRINTS";
	private final static String REEDS_GESTEMD_COUNT_SQL =
		"SELECT count(reedsgestemd) AS NUMBER_OF_ROWS FROM koa01.kiezers WHERE reedsgestemd = 'Y'";
	private final static String REEDS_GESTEMD_COUNT_SELECT_FIELD =
		"NUMBER_OF_ROWS";
	private final static String KIEZER_COUNT_SQL =
		"SELECT COUNT(*) AS NUMBER_OF_ROWS FROM koa01.KIEZERS";
	private final static String KIEZER_COUNT_SELECT_FIELD = "NUMBER_OF_ROWS";
	//SQL statement used to count the number of rows that have the field timestampsgestemd filled 
	private final static String TIMESTAMPGESTEMD_COUNT_SQL =
		"SELECT count(timestampgestemd) AS NUMBER_OF_ROWS FROM koa01.kiezers WHERE timestampgestemd IS NOT NULL";
	private final static String TIMESTAMPGESTEMD_COUNT_SELECT_FIELD =
		"NUMBER_OF_ROWS";
	//SQL statement used to count the number of rows that have the field modaliteit filled 
	private final static String MODALITEIT_COUNT_SQL =
		"SELECT count(modaliteit) AS NUMBER_OF_ROWS FROM koa01.kiezers WHERE modaliteit IS NOT NULL";
	private final static String MODALITEIT_COUNT_SELECT_FIELD =
		"NUMBER_OF_ROWS";
	//SQL statement used to count the number of invalid logins
	private final static String INVALID_LOGINS_COUNT_SQL =
		"SELECT sum(invalidlogins) AS INVALID_LOGIN_COUNT FROM koa01.kiezers WHERE invalidlogins IS NOT NULL";
	private final static String INVALID_LOGINS_COUNT_SELECT_FIELD =
		"INVALID_LOGIN_COUNT";
	//SQL statement used to count the number of invalid logins
	private final static String VALID_LOGINS_COUNT_SQL =
		"SELECT sum(validlogins) AS VALID_LOGIN_COUNT FROM koa01.kiezers WHERE validlogins IS NOT NULL";
	private final static String VALID_LOGINS_COUNT_SELECT_FIELD =
		"VALID_LOGIN_COUNT";
	//SQL statement used to count the number of rows that have the field accountlocked = 'Y'
	private final static String ACCOUNT_COUNT_SQL =
		"SELECT count(accountlocked) AS NUMBER_OF_ROWS FROM koa01.kiezers WHERE accountlocked = 'Y'";
	private final static String ACCOUNT_COUNT_SELECT_FIELD = "NUMBER_OF_ROWS";
	//SQL statement used to count the number of rows that have the field accountlocked = 'Y'
	private final static String ACCOUNTLOCKED_COUNT_SQL =
		"SELECT count(accountlocked) AS NUMBER_OF_ROWS FROM koa01.kiezers WHERE accountlocked = 'Y'";
	private final static String ACCOUNTLOCKED_COUNT_SELECT_FIELD =
		"NUMBER_OF_ROWS";
	//strings for auditing
	private final static String AUDIT_MESSAGE_FINGERPRINT_DYN_KR_ERR =
		"Vingerafdrukken dynamisch KR zijn niet gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_STAT_KR_ERR =
		"Vingerafdrukken statisch KR zijn niet gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_DYN_OK =
		"De vingerafdrukken van het dynamische deel van de KR zijn gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_STAT_OK =
		"De vingerafdrukken van het statische deel van de KR zijn gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_OK =
		"Zowel de dynamische als de statische vingerafdrukken van de KR zijn gelijk";
	private final static String AUDIT_MESSAGE_FINGERPRINT_DYN_CREATE =
		"Vingerafdruk dynamische deel van de KR is aangemaakt met waarde: ";
	private final static String AUDIT_MESSAGE_FINGERPRINT_STAT_CREATE =
		"Vingerafdruk statische deel van de KR is aangemaakt met waarde: ";
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
	 * This method initializes the KR
	 * 
	 *@return Callresult dataobject that contains the result of the initialisation.
	 * 
	 *@exception com.logicacmg.koa.exception.KOAException
	 */
	private CallResult initialize()
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KRSessionEJBBean] entered initialize()");
		boolean bSucces = true;
		Fingerprint xNewStaticFingerprint = null;
		CallResult xCallResult = new CallResult();
		//set default value
		xCallResult.setResult(CallResult.RESULT_OK);
		//check if kr is filled with data
		if (getNumberOfRows() == 0)
		{
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				"Er zijn geen kiezers ingelezen in de applicatie.");
			bSucces = false;
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KRSessionEJBBean] KR is not filled");
			xCallResult.setResult(CallResult.KR_NOT_FILLED);
		}
		//check reedsgestemd is empty
		if (getNumberOfIndicationVoted() > 0)
		{
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				"Er zijn kiezers aanwezig welke reeds gestemd hebben.");
			bSucces = false;
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KRSessionEJBBean] indication voted hasn't been removed");
			xCallResult.setResult(CallResult.KR_INIDCATION_VOTED_FILLED);
		}
		//check timestampgestemd is empty
		if (getNumberOfTimestampGestemd() > 0)
		{
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				"Er zijn kiezers aanwezig waarbij tijdstip van stemmen gevuld is.");
			bSucces = false;
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KRSessionEJBBean] timestampGestemd is filled");
			xCallResult.setResult(CallResult.KR_TIMESTAMP_VOTING_FILLED);
		}
		//check if field modaliteit is empty
		if (getNumberOfModaliteit() > 0)
		{
			KOALogHelper.audit(
				KOALogHelper.ERROR,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				"Er zijn kiezers aanwezig waarbij de modaliteit van het stemmen reeds gevuld is.");
			bSucces = false;
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KRSessionEJBBean] column modaliteit is filled");
			xCallResult.setResult(CallResult.KR_MODALITEIT_FILLED);
		}
		if (bSucces)
		{
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				"De kiezers zijn succesvol gecontroleerd en zijn correct aanwezig in de Kiezersdatabase.");
		}
		//create a new static fingerprint
		xNewStaticFingerprint = createStaticFingerprint();
		String sFingerprintMessage =
			AUDIT_MESSAGE_FINGERPRINT_STAT_CREATE
				+ KOAEncryptionUtil.fingerprintValueToString(
					xNewStaticFingerprint.getFingerprint());
		KOALogHelper.audit(
			KOALogHelper.TRACE,
			AuditEventListener.STATE_CHANGE,
			ComponentType.KR,
			getSessionContext().getCallerPrincipal().getName(),
			sFingerprintMessage);
		//get the static fingerprint created by data manager
		Fingerprint xInitStaticFingerprint =
			getLatestFingerprint(Fingerprint.KR_STATIC_FINGERPRINT);
		//store static fingerprint
		saveFingerprint(
			xNewStaticFingerprint,
			SystemState.INITIALIZED,
			Fingerprint.KR_STATIC_FINGERPRINT);
		/*
		 * compare the new created fingerprints with the ones that are created 
		 * by the data manager during import voters
		 */
		if (xInitStaticFingerprint == null
			|| !xInitStaticFingerprint.equals(xNewStaticFingerprint))
		{
			if (bSucces)
			{
				xCallResult.setResult(CallResult.FINGERPRINTS_STAT_KR_ERR);
			}
			/* log the compare of the fingerprints if not equal */
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				AUDIT_MESSAGE_FINGERPRINT_STAT_KR_ERR);
		}
		//log the fingerprint
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KRSessionEJBBean] exit initialize() with value "
				+ xCallResult.getResult());
		return xCallResult;
	}
	/**
	 * A generic method that executes SQL that contains a count or sum as the field to be selected
	 * 
	 *@return int - The result of the count or sum function
	 * 
	 *@param sSQL - The SQL query to be executed
	 *@param sField - The name of the field that refers to the count or sum function in the select statement.
	 * 				  (Tip: use the alias statement in your select statement to refger to the count or sum function)	
	 * 
	 *@exception com.logicacmg.koa.exception.KOAException
	 */
	private int executeSQL(String sSQL, String sField)
		throws com.logicacmg.koa.exception.KOAException
	{
		int iNumber = -1;
		DBUtils xDBUtils =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR));
		Connection xConn = null;
		Statement xStatement = null;
		ResultSet xRs = null;
		try
		{
			xConn = xDBUtils.getConnection();
			xStatement = xConn.createStatement();
			xRs = xDBUtils.executeResultQuery(xStatement, sSQL);
			if (xRs.next())
			{
				iNumber = xRs.getInt(sField);
			}
		}
		catch (java.sql.SQLException xSQLExc)
		{
			String[] params = { "KRSessionEJBBean" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_SQL,
				params,
				xSQLExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		finally
		{
			xDBUtils.closeResultSet(xRs);
			xDBUtils.closeStatement(xStatement);
			xDBUtils.closeConnection(xConn);
		}
		return iNumber;
	}
	/**
	 * Count the number of rows in the kiezers table
	 * 
	 * @return int - The number of rows in the table.
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getNumberOfRows()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iNoOfRows = -1;
		iNoOfRows = executeSQL(KIEZER_COUNT_SQL, KIEZER_COUNT_SELECT_FIELD);
		return iNoOfRows;
	}
	/**
	 * Counts the number of rows that have a column reedsgestemd with the valye = 'Y' (i.e. TRUE, 'N' means FALSE)
	 * 
	 * @return int - the number of rows that have a column reedsgestemd with the value 'Y'
	 *      
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getNumberOfIndicationVoted()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iNoOfRows = -1;
		iNoOfRows =
			executeSQL(
				REEDS_GESTEMD_COUNT_SQL,
				REEDS_GESTEMD_COUNT_SELECT_FIELD);
		return iNoOfRows;
	}
	/**
	 * Counts the number of rows that have a column timestampvoted that's not null
	 * 
	 * @return int - the number of rows that have the column timestampgestemd filled(= not null)
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getNumberOfTimestampGestemd()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iNoOfRows = -1;
		iNoOfRows =
			executeSQL(
				TIMESTAMPGESTEMD_COUNT_SQL,
				TIMESTAMPGESTEMD_COUNT_SELECT_FIELD);
		return iNoOfRows;
	}
	/**
	 * Counts the number of rows that have a column MODALITEIT that's not null
	 * 
	 * @return int - the number of rows that have the column modaliteit filled(= not null)
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getNumberOfModaliteit()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iNoOfRows = -1;
		iNoOfRows =
			executeSQL(MODALITEIT_COUNT_SQL, MODALITEIT_COUNT_SELECT_FIELD);
		return iNoOfRows;
	}
	/**
	 * Counts the number of rows that have a column accountlocked = 'Y'
	 * 
	 * @return int - the number of rows that have the column accountlocked= 'Y'
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getNumberOfAccountLocked()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iNoOfRows = -1;
		iNoOfRows =
			executeSQL(
				ACCOUNTLOCKED_COUNT_SQL,
				ACCOUNTLOCKED_COUNT_SELECT_FIELD);
		return iNoOfRows;
	}
	/**
	 * Counts the number of invalid logins
	 * 
	 * @return int - the number of invalid logins
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private int getSumInvalidLogins()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iSum = -1;
		iSum =
			executeSQL(
				INVALID_LOGINS_COUNT_SQL,
				INVALID_LOGINS_COUNT_SELECT_FIELD);
		return iSum;
	}
	/**
	* Counts the number of valid logins
	* 
	* @return int - the number of valid logins
	* 
	* @exception com.logicacmg.koa.exception.KOAException
	*/
	private int getSumValidLogins()
		throws com.logicacmg.koa.exception.KOAException
	{
		int iSum = -1;
		iSum =
			executeSQL(VALID_LOGINS_COUNT_SQL, VALID_LOGINS_COUNT_SELECT_FIELD);
		return iSum;
	}
	/**
	
	 * This method creates a fingerprint over the dynamic part of the KR
	 * 
	 * @return Returns a Fingerprint data object.
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Fingerprint createDynamicFingerprint()
		throws com.logicacmg.koa.exception.KOAException
	{
		com.logicacmg.koa.dataobjects.Fingerprint xFingerprint =
			new com.logicacmg.koa.dataobjects.Fingerprint();
		xFingerprint.setFingerprint(
			KOAEncryptionUtil.getFingerPrint(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR),
				TechnicalProps.KR_SCHEMA_NAME,
				TechnicalProps.KR_TABLE_NAME,
				TechnicalProps.KR_DYNAMIC_COLUMNS,
				TechnicalProps.KR_SORT_KEY));
		xFingerprint.setFingerprintType(Fingerprint.KR_DYNAMIC_FINGERPRINT);
		xFingerprint.setTimestamp(
			new java.sql.Timestamp(System.currentTimeMillis()));
		String sFingerprintMessage =
			AUDIT_MESSAGE_FINGERPRINT_DYN_CREATE
				+ KOAEncryptionUtil.fingerprintValueToString(
					xFingerprint.getFingerprint());
		KOALogHelper.audit(
			KOALogHelper.TRACE,
			AuditEventListener.STATE_CHANGE,
			ComponentType.KR,
			getSessionContext().getCallerPrincipal().getName(),
			sFingerprintMessage);
		return xFingerprint;
	}
	/**
	 *  This method creates a fingerprint over the static part of the KR
	 * 
	 * @return Returns a Fingerprint data object.
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Fingerprint createStaticFingerprint()
		throws com.logicacmg.koa.exception.KOAException
	{
		com.logicacmg.koa.dataobjects.Fingerprint xFingerprint =
			new com.logicacmg.koa.dataobjects.Fingerprint();
		xFingerprint.setFingerprint(
			KOAEncryptionUtil.getFingerPrint(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR),
				TechnicalProps.KR_SCHEMA_NAME,
				TechnicalProps.KR_TABLE_NAME,
				TechnicalProps.KR_STATIC_COLUMNS,
				TechnicalProps.KR_SORT_KEY));
		xFingerprint.setFingerprintType(Fingerprint.KR_STATIC_FINGERPRINT);
		xFingerprint.setTimestamp(
			new java.sql.Timestamp(System.currentTimeMillis()));
		return xFingerprint;
	}
	/**
	 *  This method performs action when the system state is going to be changed.
	 * 
	 *  Note: The system isn't in the new state yet, this method performs the actions needed
	 *        for the transition to the new state! 
	 * 
	 * @param sCurrentState The current state the system is in
	 * @param newState int Indication of the new system state. 
	 *                     (The value comes from the SystemState class)
	 * 
	 * 
	 * @return CallResult object that contains the result of the performed actions.
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public void changeState(String sCurrentState, String sNewState)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] entered changeState()");
		if (sNewState == null)
		{
			throw new KOAException(ErrorConstants.KR_STATE_TRANSITION_ERROR);
		}
		CallResult xCallResult = new CallResult();
		xCallResult.setResult(CallResult.RESULT_OK);
		if (sNewState.equals(SystemState.INITIALIZED))
		{
			xCallResult = initialize();
		}
		else if (sNewState.equals(SystemState.SUSPENDED))
		{
			xCallResult = checkKR(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.CLOSED))
		{
			xCallResult = checkKR(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.RE_INITIALIZED))
		{
			xCallResult = checkKR(sCurrentState, sNewState);
		}
		else if (sNewState.equals(SystemState.READY_TO_COUNT))
		{
			xCallResult = checkKR(sCurrentState, sNewState);
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
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KRSessionEJBBean] State paramater has an invalid value");
			throw new KOAException(ErrorConstants.KR_STATE_TRANSITION_ERROR);
		}
		if (xCallResult.getResult() == CallResult.FINGERPRINTS_STAT_KR_ERR)
		{
			throw new KOAException(ErrorConstants.STATIC_KR_FINGERPRINT_ERROR);
		}
		if (xCallResult.getResult() == CallResult.FINGERPRINTS_DYN_KR_ERR)
		{
			throw new KOAException(ErrorConstants.DYNAMIC_KR_FINGERPRINT_ERROR);
		}
		if (xCallResult.getResult() != CallResult.RESULT_OK)
		{
			throw new KOAException(ErrorConstants.KR_STATE_TRANSITION_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] leaving changeState()");
	}
	/**
	 * This method handles te actions that have to be performed for the KR component
	 * when the system transits to the blocked state.
	 * 
	 * @return CallResult object 
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private CallResult block() throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] entered block()");
		Fingerprint xNewStaticFingerprint = null, xInitStaticFingerprint = null;
		CallResult xCallResult = new CallResult();
		//set default value
		xCallResult.setResult(CallResult.RESULT_OK);
		//create a new static fingerprint
		xNewStaticFingerprint = createStaticFingerprint();
		if (xNewStaticFingerprint == null)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KRSessionEJBBean] Unable to create a new static fingerprint");
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		//get the static fingerprint created at initialize
		xInitStaticFingerprint =
			getLatestFingerprint(Fingerprint.KR_STATIC_FINGERPRINT);
		//store static fingerprint
		saveFingerprint(
			xNewStaticFingerprint,
			SystemState.BLOCKED,
			Fingerprint.KR_STATIC_FINGERPRINT);
		if (xInitStaticFingerprint == null
			|| !xInitStaticFingerprint.equals(xNewStaticFingerprint))
		{
			xCallResult.setResult(CallResult.FINGERPRINTS_STAT_KR_ERR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] leaving block() with value "
				+ xCallResult.getResult());
		return xCallResult;
	}
	/**
	 * This method handles the actions that have to be performed for the KR component when the 
	 * system transits to one of te following states:
	 * SUSPENDED
	 * CLOSED
	 * REINITIALIZED
	 * READY_TO_COUNT
	 * 
	 * @param sCurrentState The current state the system is in
	 * @param sNewState The new system state.
	 * 
	 * @return CallResult object 
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private CallResult checkKR(String sCurrentState, String sNewState)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] entered checkKR()");
		boolean bFingerprintsStaticChecked = false;
		boolean bFingerprintsDynamicChecked = false;
		boolean bFingerprintsStaticAreEqual = true;
		boolean bFingerprintsDynamicAreEqual = true;
		Fingerprint xNewStaticFingerprint = null,
			xNewDynamicFingerprint = null,
			xLastStaticFingerprint = null,
			xLastDynamicFingerprint = null;
		CallResult xCallResult = new CallResult();
		//set default value
		xCallResult.setResult(CallResult.RESULT_OK);
		if (!sNewState.equals(SystemState.OPEN)
			&& !sNewState.equals(SystemState.VOTES_COUNTED))
		{
			//create a new static fingerprint
			xNewStaticFingerprint = createStaticFingerprint();
			String sFingerprintMessage =
				AUDIT_MESSAGE_FINGERPRINT_STAT_CREATE
					+ KOAEncryptionUtil.fingerprintValueToString(
						xNewStaticFingerprint.getFingerprint());
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				sFingerprintMessage);
			if (xNewStaticFingerprint == null)
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[KRSessionEJBBean] Unable to create a new static fingerprint");
				throw new KOAException(ErrorConstants.KR_ERROR);
			}
		}
		/* only create dynamic fingerprint when needed */
		if (sNewState.equals(SystemState.SUSPENDED)
			|| sNewState.equals(SystemState.CLOSED)
			|| sNewState.equals(SystemState.RE_INITIALIZED)
			|| sNewState.equals(SystemState.READY_TO_COUNT))
		{
			//create a new dynamic fingerprint
			xNewDynamicFingerprint = createDynamicFingerprint();
			if (xNewDynamicFingerprint == null)
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[KRSessionEJBBean] Unable to create a new dynamic fingerprint");
				throw new KOAException(ErrorConstants.KR_ERROR);
			}
		}
		/*  only get latest static fingerprint in these new states,
			now compare the fingerprints */
		if (sNewState.equals(SystemState.SUSPENDED)
			|| sNewState.equals(SystemState.CLOSED)
			|| sNewState.equals(SystemState.RE_INITIALIZED)
			|| sNewState.equals(SystemState.BLOCKED)
			|| sNewState.equals(SystemState.READY_TO_COUNT))
		{
			xLastStaticFingerprint =
				getLatestFingerprint(Fingerprint.KR_STATIC_FINGERPRINT);
			/*
			 * compare the new created fingerprints with the ones that are created 
			 * during the initialize state.
			 */
			if (xLastStaticFingerprint == null
				|| !xLastStaticFingerprint.equals(xNewStaticFingerprint))
			{
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[KRSessionEJBBean.checkKR] Static fingerprints are not equal.");
				xCallResult.setResult(CallResult.FINGERPRINTS_STAT_KR_ERR);
				bFingerprintsStaticAreEqual = false;
				/* log the compare of the fingerprints if not equal */
				KOALogHelper.audit(
					KOALogHelper.TRACE,
					AuditEventListener.STATE_CHANGE,
					ComponentType.KR,
					getSessionContext().getCallerPrincipal().getName(),
					AUDIT_MESSAGE_FINGERPRINT_STAT_KR_ERR);
			}
			bFingerprintsStaticChecked = true;
		}
		/* check dynamic fingerprint for other states also */
		if (sNewState.equals(SystemState.RE_INITIALIZED)
			|| sNewState.equals(SystemState.READY_TO_COUNT)
			|| (sNewState.equals(SystemState.CLOSED)
				&& sCurrentState.equals(SystemState.SUSPENDED)))
		{
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KRSessionEJBBean.checkKR] checkingDynamic FP");
			//try to get the dynamic fingerprint created at block state
			xLastDynamicFingerprint =
				getLatestFingerprint(Fingerprint.KR_DYNAMIC_FINGERPRINT);
			if (xLastDynamicFingerprint == null
				|| !xLastDynamicFingerprint.equals(xNewDynamicFingerprint))
			{
				xCallResult.setResult(CallResult.FINGERPRINTS_DYN_KR_ERR);
				bFingerprintsDynamicAreEqual = false;
				/* log the comparison of the fingerprints */
				KOALogHelper.audit(
					KOALogHelper.TRACE,
					AuditEventListener.STATE_CHANGE,
					ComponentType.KR,
					getSessionContext().getCallerPrincipal().getName(),
					AUDIT_MESSAGE_FINGERPRINT_DYN_KR_ERR);
			}
			bFingerprintsDynamicChecked = true;
		}
		/* Save the fingerprints at the end, so we can fetch the last created first */
		//store static fingerprint
		saveFingerprint(
			xNewStaticFingerprint,
			sNewState,
			Fingerprint.KR_STATIC_FINGERPRINT);
		//store dynamic fingerprint
		saveFingerprint(
			xNewDynamicFingerprint,
			sNewState,
			Fingerprint.KR_DYNAMIC_FINGERPRINT);
		if (bFingerprintsDynamicChecked
			&& !bFingerprintsStaticChecked
			&& bFingerprintsDynamicAreEqual)
		{
			// only dynamic has been checked
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				AUDIT_MESSAGE_FINGERPRINT_DYN_OK);
		}
		else if (
			!bFingerprintsDynamicChecked
				&& bFingerprintsStaticChecked
				&& bFingerprintsStaticAreEqual)
		{
			// only static has been checked		
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				AUDIT_MESSAGE_FINGERPRINT_STAT_OK);
		}
		else if (
			bFingerprintsDynamicChecked
				&& bFingerprintsStaticChecked
				&& bFingerprintsDynamicAreEqual
				&& bFingerprintsStaticAreEqual)
		{
			// both static and dynamci are checked
			KOALogHelper.audit(
				KOALogHelper.TRACE,
				AuditEventListener.STATE_CHANGE,
				ComponentType.KR,
				getSessionContext().getCallerPrincipal().getName(),
				AUDIT_MESSAGE_FINGERPRINT_OK);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] leaving checkKR() with value "
				+ xCallResult.getResult());
		return xCallResult;
	}
	/**
	 * Retrieves the last created fingerprint from the database
	 *      
	 * @param iType - The type of fingerprint to be retrieved (i.e. the static or dynamic fingerprint)
	 * 
	 * @return KRFingerprint entity bean when an occurance was found, null when nothing was found
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private KRFingerprints getFingerprintEJB(int iType)
		throws com.logicacmg.koa.exception.KOAException
	{
		KRFingerprints xKRFingerprints = null;
		try
		{
			KRFingerprintsHome xKRFingerprintsHome =
				ObjectCache.getInstance().getKRFingerprintsHome();
			xKRFingerprints =
				xKRFingerprintsHome.findLatestFingerprint(new Integer(iType));
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "KRFingerprint" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		catch (javax.ejb.FinderException xFinderExc)
		{
			String[] params = { "KRFingerprint" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderExc);
		}
		return xKRFingerprints;
	}
	/**
	 * Retrieves a dynamic or static fingerprint from the database for a certain systemstate
	 *      
	 * @param iType - The type of fingerprint to be retrieved (i.e. the static or dynamic fingerprint)
	 * @param sSystemState - The state of the system the fingerprint was stored
	 * 
	 * @return Fingerprint dataobject when an occurance was found, null when nothing was found
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Fingerprint getLatestFingerprint(int iType)
		throws com.logicacmg.koa.exception.KOAException
	{
		Fingerprint xFingerprint = null;
		KRFingerprints xKRFingerprints = getFingerprintEJB(iType);
		if (xKRFingerprints != null)
		{
			xFingerprint = fillFingerprint(xKRFingerprints, iType);
		}
		return xFingerprint;
	}
	/**
	 * Converts a fingerprint entity bean into a fingerprint dataobject
	 *      
	 * @param iType - The type of fingerprint 
	 * @param xKRFingerprints = The entity bean to be converted
	 * 
	 * @return Fingerpint data object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private Fingerprint fillFingerprint(
		KRFingerprints xKRFingerprints,
		int iType)
		throws com.logicacmg.koa.exception.KOAException
	{
		Fingerprint xFingerprint = new Fingerprint();
		try
		{
			xFingerprint.setFingerprint(xKRFingerprints.getFingerprint());
			xFingerprint.setFingerprintType(iType);
			xFingerprint.setTimestamp(xKRFingerprints.getTimestamp());
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Fingerprint" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		return xFingerprint;
	}
	/**
	 * Stores a fingeprint
	 *      
	 * @param iType - The type of fingerprint 
	 * @param xFingeprint - Dataobject taht contains the fingerprint to be stored
	 * @param sState - The systemstate to store the fingerprint
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private void saveFingerprint(
		Fingerprint xFingerprint,
		String sState,
		short iType)
		throws com.logicacmg.koa.exception.KOAException
	{
		if (xFingerprint == null)
		{
			return;
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] entered saveFingerprint()");
		KRFingerprints xKRFingerprints = null;
		try
		{
			//get new id
			BigDecimal xKey = getNewID();
			if (xKey != null)
			{
				//create new bean
				KRFingerprintsHome xKRFingerprintsHome =
					ObjectCache.getInstance().getKRFingerprintsHome();
				xKRFingerprints =
					xKRFingerprintsHome.create(
						xKey,
						new Short(iType),
						xFingerprint.getFingerprint(),
						xFingerprint.getTimestamp(),
						sState);
			}
		}
		catch (javax.ejb.CreateException xCreateException)
		{
			String[] params = { "KRFingerprints" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_CREATE,
				params,
				xCreateException);
			xCreateException.printStackTrace();
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "KRFingerprints" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			xRemoteExc.printStackTrace();
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KRSessionEJBBean] leaving saveFingerprint()");
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
		try
		{
			KRSequenceEJBHome xKRSequenceEJBHome =
				ObjectCache.getInstance().getKRSequenceEJBHome();
			KRSequenceEJB xKRSequenceEJB =
				xKRSequenceEJBHome.findByPrimaryKey(
					new KRSequenceEJBKey(KRSEQUENCE_TABLENAME));
			if (xKRSequenceEJB != null)
			{
				//retrieve the last generated id
				xNewID = xKRSequenceEJB.getNextID();
				if (xNewID != null)
				{
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[KRSessionEJBBean] old id = " + xNewID);
					//create new id
					xNewID = xNewID.add(new BigDecimal(1));
					//store the new id
					xKRSequenceEJB.setNextID(xNewID);
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[KRSessionEJBBean] new id = "
							+ xKRSequenceEJB.getNextID());
				}
			}
		}
		catch (javax.ejb.FinderException xFinderException)
		{
			String[] params = { "KRSequence" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderException);
			xFinderException.printStackTrace();
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "KRSequence" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			xRemoteExc.printStackTrace();
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		return xNewID;
	}
	/**
	 * Creates a hash over a plain password
	 * 
	 * @param sWachtwoord - The plain password to be hashed
	 * 
	 * @return String - that contains the hash over the plain password
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	private String hashWachtwoord(String sWachtwoord)
		throws com.logicacmg.koa.exception.KOAException
	{
		return KOAEncryptionUtil.hashPassword(sWachtwoord);
	}
	/**
	 * Verifies if a kiezer , indicated by param sStemcode is valid
	 * 
	 * @param sStemcode - The stemcode of the kiezer
	 * @param sWachtwoord - the plain value of the kiezers password
	 * @param bUpdateCounters - a boolean that indicates of the counters of the KR must be updated
	 * 							TRUE - Counters are updated
	 * 							FALSE - Counters are not updated
	 * 
	 * @return Stemtransactie data object
	 */
	public StemTransactie verifyKiezer(
		String sStemcode,
		String sWachtwoord,
		String sModaliteit,
		boolean bUpdateCounters)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KRSessionEJBBEan] entering verifyKiezer()");
		StemTransactie xStemTransactie = new StemTransactie();
		try
		{
			Kiezers xKiezer = null;
			xStemTransactie.Stemcode = sStemcode;
			xStemTransactie.VoteStatus = StemTransactie.OK;
			//check if the election = open
			String sCurrentState = getCurrentSystemState();
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
			// election is open, check if input fields have values
			if (xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				if (sStemcode == null || "".equals(sStemcode))
				{
					KOALogHelper.log(
						KOALogHelper.ERROR,
						"[KRSessionEJBBEan] Stemcode is null");
					xStemTransactie.VoteStatus =
						StemTransactie.INVALID_CREDENTIALS;
					/* Adding audit message for unknown voter */
					KOALogHelper.audit(
						KOALogHelper.WARNING,
						AuditEventListener.VOTER,
						ComponentType.KR,
						"Onbekende stemcode",
						"Een kiezer met stemcode ["
							+ sStemcode
							+ "] heeft getracht in te loggen via modaliteit "
							+ sModaliteit
							+ " met een stemcode welke niet voorkomt.");
					return xStemTransactie;
				}
				if (sWachtwoord == null || "".equals(sWachtwoord))
				{
					KOALogHelper.log(
						KOALogHelper.ERROR,
						"[KRSessionEJBBEan] Toegangscode is niet ingevuld");
					xStemTransactie.VoteStatus =
						StemTransactie.INVALID_CREDENTIALS;
					for (int i = 0; i < sStemcode.length(); i++)
					{
						char cCharFromStemcode = sStemcode.charAt(i);
						// check if character is numeric
						if (!Character.isDigit(cCharFromStemcode))
						{
							KOALogHelper.audit(
								KOALogHelper.WARNING,
								AuditEventListener.VOTER,
								ComponentType.KR,
								"Geen toegangscode",
								"Een kiezer heeft getracht in te loggen via modaliteit "
									+ sModaliteit
									+ " met een niet numerieke stemcode en zonder een toegangscode in te voeren.");
							return xStemTransactie;
						}
					}
					if (sStemcode.length() > 9)
					{
						KOALogHelper.audit(
							KOALogHelper.WARNING,
							AuditEventListener.VOTER,
							ComponentType.KR,
							"Geen toegangscode",
							"Een kiezer heeft getracht in te loggen via modaliteit "
								+ sModaliteit
								+ " met een stemcode met een lengte groter dan 9 en zonder een toegangscode in te voeren.");
					}
					else
					{
						KOALogHelper.audit(
							KOALogHelper.WARNING,
							AuditEventListener.VOTER,
							ComponentType.KR,
							"Geen toegangscode",
							"Een kiezer met stemcode ["
								+ sStemcode
								+ "] heeft getracht in te loggen via modaliteit "
								+ sModaliteit
								+ " zonder een toegangscode in te voeren.");
					}
					return xStemTransactie;
				}
			}
			// election is open en input fields have values. Check if these values are syntactically correct. 
			if (xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				// check if stemcode only consists of digits
				for (int i = 0; i < sStemcode.length(); i++)
				{
					char cCharFromStemcode = sStemcode.charAt(i);
					// check if character is numeric
					if (!Character.isDigit(cCharFromStemcode))
					{
						KOALogHelper.log(
							KOALogHelper.ERROR,
							"[KRSessionEJBBean] Stemcode is niet numeriek");
						xStemTransactie.VoteStatus =
							StemTransactie.NON_NUMERIC_CODE;
						return xStemTransactie;
					}
				}
				// check if stemcode is exactly 9 digits
				if (sStemcode.length() != 9)
				{
					KOALogHelper.log(
						KOALogHelper.ERROR,
						"[KRSessionEJBBean] Stemcode bestaat niet uit 9 cijfers");
					xStemTransactie.VoteStatus = StemTransactie.NINE_DIGITS;
					return xStemTransactie;
				}
				// input fields are syntactically correct. Check now if the stemcode exist.
				xKiezer = getKiezerByStemcode(sStemcode);
				// If kiezer(stemcode) does not exist, write to the audit log and set the stemtransactie votestatus to INVALID_CREDENTIALS
				if (xKiezer == null)
				{
					xStemTransactie.VoteStatus =
						StemTransactie.INVALID_CREDENTIALS;
					KOALogHelper.audit(
						KOALogHelper.WARNING,
						AuditEventListener.VOTER,
						ComponentType.KR,
						"Onbekende stemcode",
						"Een kiezer met stemcode ["
							+ sStemcode
							+ "] heeft getracht in te loggen via modaliteit "
							+ sModaliteit
							+ " met onbekende stemcode.");
				}
			}
			// Election is open and kiezer(stemcode) exists.
			if (xKiezer != null
				&& xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				//check if password, stored in the KR database, is same as the input field password 
				String sHashedPassword = hashWachtwoord(sWachtwoord);
				String sKiezerPassword = xKiezer.getHashedwachtwoord();
				if (sKiezerPassword == null
					|| !sKiezerPassword.equals(sHashedPassword))
				{
					Timestamp tsCurrentTimestamp =
						new Timestamp(System.currentTimeMillis());
					if (bUpdateCounters)
					{
						/* get the number of loggins and add one */
						Integer iInvalidLogins = xKiezer.getInvalidlogins();
						Integer iLoginAttemptsLeft =
							xKiezer.getLoginattemptsleft();
						if (iInvalidLogins == null)
						{
							//default the value to 0 when the field is empty
							iInvalidLogins = new Integer(0);
						}
						/* add one to the kiezer number of invalid logins */
						iInvalidLogins =
							new Integer(iInvalidLogins.intValue() + 1);
						xKiezer.setInvalidlogins(iInvalidLogins);
						int log_invalid_nr_logins =
							FunctionalProps.getIntProperty(
								FunctionalProps.INVALID_NR_LOGIN_LOG);
						if (iInvalidLogins.intValue() == log_invalid_nr_logins)
						{
							KOALogHelper.log(
								KOALogHelper.WARNING,
								"[KRSessionEJBBean.verifyKeizer] Kiezer heeft al "
									+ log_invalid_nr_logins
									+ " keer geprobeerd in te loggen.");
						}
						/* only lower the login attempts left when the user is not blocked. */
						if (xKiezer.getTimestampunlock() == null
							|| !xKiezer.getTimestampunlock().after(
								tsCurrentTimestamp))
						{
							xKiezer.setLoginattemptsleft(
								new Integer(iLoginAttemptsLeft.intValue() - 1));
						}
						if (iLoginAttemptsLeft == null
							|| (iLoginAttemptsLeft.intValue() - 1) <= 0)
						{
							iLoginAttemptsLeft = new Integer(getNrTimesLogin());
							xKiezer.setLoginattemptsleft(iLoginAttemptsLeft);
							/* create timestamp when login is possible again */
							int iUnlockTimeInMillis = 0;
							try
							{
								iUnlockTimeInMillis =
									1000
										* 60
										* FunctionalProps.getIntProperty(
											FunctionalProps
												.LOGIN_TIME_TO_UNLOCK);
							}
							catch (Exception e)
							{
								KOALogHelper.log(
									KOALogHelper.WARNING,
									"[KRSessionEJBBean.verifyKiezer] Could not find property for unlocktime... Default value of 15 minutes used...");
								iUnlockTimeInMillis = 1000 * 60 * 15;
								// default
							}
							java.sql.Timestamp ts =
								new java.sql.Timestamp(
									System.currentTimeMillis()
										+ iUnlockTimeInMillis);
							/* Lock the account and set the time the account will be unlocked */
							/* Only set the account locked timestamp when the account is not yet locked */
							if (!xKiezer.getAccountlocked().booleanValue())
							{
								xKiezer.setAccountlocked(new Boolean(true));
								xKiezer.setTimestampunlock(ts);
								KOALogHelper.audit(
									KOALogHelper.WARNING,
									AuditEventListener.VOTER,
									ComponentType.KR,
									"Stemcode " + sStemcode,
									"De kiezer met stemcode ["
										+ sStemcode
										+ "] is geblokkeerd tot "
										+ ts.toString());
							}
							/* reset the number of attempts left */
							xKiezer.setLoginattemptsleft(
								new Integer(getNrTimesLogin()));
							/* set the vote status */
							xStemTransactie.VoteStatus =
								StemTransactie.ACCOUNT_LOCKED;
						}
						else
						{
							/* If not update the counters make a difference between account locked and invalid credits */
							if (xKiezer.getAccountlocked().booleanValue()
								&& xKiezer.getTimestampunlock().after(
									tsCurrentTimestamp))
							{
								/* set the vote status */
								xStemTransactie.VoteStatus =
									StemTransactie.ACCOUNT_LOCKED;
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
							}
							else
							{
								if (xKiezer.getAccountlocked().booleanValue()
									&& !xKiezer.getTimestampunlock().after(
										tsCurrentTimestamp))
								{
									xKiezer.setAccountlocked(
										new Boolean(false));
									xKiezer.setTimestampunlock(null);
								}
								/* set the return value */
								xStemTransactie.VoteStatus =
									StemTransactie.INVALID_CREDENTIALS;
								/* Adding audit message for invalid credentials */
								KOALogHelper.audit(
									KOALogHelper.WARNING,
									AuditEventListener.VOTER,
									ComponentType.KR,
									"Stemcode " + sStemcode,
									"De kiezer met stemcode ["
										+ sStemcode
										+ "] heeft getracht in te loggen via modaliteit "
										+ sModaliteit
										+ " met een incorrecte toegangscode ["
										+ sHashedPassword
										+ "].");
							}
						}
					} //end if update counters
					else
					{
						/* If not update the counters make a difference between account locked and invalid credits */
						if (xKiezer.getAccountlocked().booleanValue()
							&& xKiezer.getTimestampunlock().after(
								tsCurrentTimestamp))
						{
							/* set the vote status */
							xStemTransactie.VoteStatus =
								StemTransactie.ACCOUNT_LOCKED;
						}
						else
						{
							if (xKiezer.getAccountlocked().booleanValue()
								&& !xKiezer.getTimestampunlock().after(
									tsCurrentTimestamp))
							{
								xKiezer.setAccountlocked(new Boolean(false));
								xKiezer.setTimestampunlock(null);
							}
							/* set the return value */
							xStemTransactie.VoteStatus =
								StemTransactie.INVALID_CREDENTIALS;
						}
					} //end when not update counters
				}
			}
			//check if kiezer is not blocked 
			if (xKiezer != null
				&& xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				Boolean bAccountLocked = xKiezer.getAccountlocked();
				/* Added the check for the check on the time for unlock  */
				Timestamp tsTimestamp = xKiezer.getTimestampunlock();
				/* Added extra check on the timestamp  */
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
					/* Reset the timestamp for unlocking  */
					xKiezer.setTimestampunlock(null);
				}
			}
			//check if kiezer hasn't voted yet
			if (xKiezer != null
				&& xStemTransactie.VoteStatus == StemTransactie.OK)
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
			/* check if the account is marked as deleted*/
			if (xKiezer != null
				&& xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				Boolean bDeleted = xKiezer.getVerwijderd();
				if (bDeleted != null && bDeleted.equals(Boolean.TRUE))
				{
					/* say the account is locked */
					xStemTransactie.VoteStatus = StemTransactie.KIEZER_DELETED;
				}
			}
			/* if none of the above, we can say verification is succesfull */
			if (xKiezer != null
				&& xStemTransactie.VoteStatus == StemTransactie.OK)
			{
				/* set the last succesful login */
				java.sql.Timestamp ts =
					new java.sql.Timestamp(System.currentTimeMillis());
				xKiezer.setTimelastsuccesfullogin(ts);
				if (bUpdateCounters)
				{
					Integer iValidLogins = xKiezer.getValidlogins();
					if (iValidLogins == null)
					{
						iValidLogins = new Integer(0);
					}
					iValidLogins = new Integer(iValidLogins.intValue() + 1);
					xKiezer.setValidlogins(iValidLogins);
				}
			}
			if (xKiezer != null)
			{
				xStemTransactie.kiezer = kiezerEJBToKiezerDataObject(xKiezer);
				xStemTransactie.VotingTime =
					xStemTransactie.kiezer.timestampGestemd;
				xStemTransactie.Modaliteit = xStemTransactie.kiezer.modaliteit;
			}
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KRSessionEJBBEan] leaving verifyKiezer()");
		return xStemTransactie;
	}
	/**
	 * Gets the nr of times to login from the functional props.
	 * 
	 * @return int - The number of time s to login from the functional props, when not found it returns the default value of 3
	 */
	private int getNrTimesLogin()
	{
		int iNrTimesLogin = 0;
		try
		{
			iNrTimesLogin =
				FunctionalProps.getIntProperty(
					FunctionalProps.LOGIN_NR_TIMES_LOGIN);
		}
		catch (Exception e)
		{
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"[KRSessionEJBBean.verifyKiezer] Could not find property for nr of times to login... Default value of 3 times used...");
			iNrTimesLogin = 3; //by default
		}
		return iNrTimesLogin;
	}
	public String getCurrentSystemState()
		throws com.logicacmg.koa.exception.KOAException
	{
		String sCurrentState = null;
		try
		{
			Koa_state xState = ObjectCache.getInstance().getState();
			if (xState != null)
			{
				sCurrentState = xState.getCurrent_state();
			}
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "KOA State" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		return sCurrentState;
	}
	/**
	 * This method marks a kiezer as already voted, sets the timestamp of hte voting and the 
	 * source(modaliteit) of which the vote originated from.
	 * 
	 * Note: This method has to be configured to participate in a existing transaction
	 * 
	 * @param xKiezer- Kiezer data object that contains the fiels to be 
	 *                 updated (modaliteit, timestampGestemd) and the primary key(stemcode)
	 * 
	 */
	public void kiezerHeeftGestemd(Kiezer xKiezer)
		throws com.logicacmg.koa.exception.KOAException
	{
		if (xKiezer == null
			|| xKiezer.stemcode == null
			|| xKiezer.stemcode.length() == 0
			|| xKiezer.timestampGestemd == null
			|| xKiezer.modaliteit == null
			|| xKiezer.modaliteit.length() == 0)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KRSessionEJBBean] kiezerHeeftGestemd() one or more required fields are missing");
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		try
		{
			Kiezers xKiezerEJB = getKiezerByStemcode(xKiezer.stemcode);
			if (xKiezer == null)
			{
				KOALogHelper.log(
					KOALogHelper.WARNING,
					"[KRSessionEJBBean] kiezerHeeftGestemd() Kiezer object is null");
			}
			xKiezerEJB.setReedsgestemd(new Boolean(true));
			xKiezerEJB.setTimestampGestemd(xKiezer.timestampGestemd);
			xKiezerEJB.setModaliteit(xKiezer.modaliteit);
			xKiezerEJB.setTransactienummer(xKiezer.transactionNumber);
		}
		catch (java.rmi.RemoteException xRmiExc)
		{
			String[] params = { "Kiezer EJB" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRmiExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		catch (Exception e)
		{
			KOALogHelper.logError(
				"KRSessionEJBBean",
				"Could not proces the vote in the KR database",
				e);
		}
	}
	/**
	 * Searches a kiezer by it's primary key
	 * 
	 * @return a Kiezers entity bean
	 */
	private Kiezers getKiezerByStemcode(String sStemcode)
		throws com.logicacmg.koa.exception.KOAException
	{
		Kiezers xKiezer = null;
		try
		{
			KiezersHome xKiezersHome =
				ObjectCache.getInstance().getKiezersHome();
			xKiezer = xKiezersHome.findByPrimaryKey(new KiezersKey(sStemcode));
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException("");
		}
		catch (javax.ejb.FinderException xFinderExc)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"[KRSessionEJBBean]",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderExc);
			xKiezer = null;
		}
		return xKiezer;
	}
	/**
	 * Selects the kiezer indicatied by the param sStemcode
	 * 
	 * @param sStemcode - The key to search the kiezer
	 * 
	 * @return Kiezer data object with the available data of the kiezer, 
	 * 			NULL - when the kiezer is not found
	 */
	public Kiezer getKiezer(String sStemcode)
		throws com.logicacmg.koa.exception.KOAException
	{
		Kiezer xKiezer = null;
		Kiezers xKiezersEJB = getKiezerByStemcode(sStemcode);
		if (xKiezersEJB != null)
		{
			xKiezer = kiezerEJBToKiezerDataObject(xKiezersEJB);
		}
		return xKiezer;
	}
	/**
	 * convert a kiezers entity bean to a kiezers dataobject
	 * 
	 * @param Kiezers - The EJB to be converted
	 * 
	 * @return Kiezer data object with the available data of the kiezer, 
	 * 			
	 */
	private Kiezer kiezerEJBToKiezerDataObject(Kiezers xKiezersEJB)
		throws com.logicacmg.koa.exception.KOAException
	{
		Kiezer xKiezer = null;
		try
		{
			xKiezer = new Kiezer();
			xKiezer.accountLocked = xKiezersEJB.getAccountlocked();
			xKiezer.reedsGestemd = xKiezersEJB.getReedsgestemd();
			xKiezer.kiezerIdentificatie = xKiezersEJB.getKiezeridentificatie();
			xKiezer.districtnummer = xKiezersEJB.getDistrictnummer();
			xKiezer.hashedWachtwooord = xKiezersEJB.getHashedwachtwoord();
			xKiezer.kieskringnummer = xKiezersEJB.getKieskringnummer();
			xKiezer.loginsAttempsLeft = xKiezersEJB.getLoginattemptsleft();
			xKiezer.stemcode = xKiezersEJB.getStemcode();
			xKiezer.timeLastSuccesfullLogin =
				xKiezersEJB.getTimelastsuccesfullogin();
			xKiezer.timestampUnlock = xKiezersEJB.getTimestampunlock();
			xKiezer.invalidLogins = xKiezersEJB.getInvalidlogins();
			xKiezer.transactionNumber = xKiezersEJB.getTransactienummer();
			xKiezer.timestampGestemd = xKiezersEJB.getTimestampGestemd();
			xKiezer.modaliteit = xKiezersEJB.getModaliteit();
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"KRSessionEJBBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
		return xKiezer;
	}
	/**
	 * Collects the counters
	 * 
	 * @param sComponmetID - Teh id to register the counters of the KR
	 * 
	 * @return CounterData object
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public CounterData collectCounters(String sComponentID)
		throws com.logicacmg.koa.exception.KOAException
	{
		CounterData xCounterData =
			new CounterData(ComponentType.KR, sComponentID);
		xCounterData.setCounter(
			CounterKeys.STEMMEN_UITGEBRACHT,
			getNumberOfIndicationVoted());
		xCounterData.setCounter(
			CounterKeys.ACCOUNT_LOCK,
			getNumberOfAccountLocked());
		xCounterData.setCounter(
			CounterKeys.VERIFICATIE_GELUKT,
			getSumValidLogins());
		xCounterData.setCounter(
			CounterKeys.VERIFICATIE_MISLUKT,
			getSumInvalidLogins());
		return xCounterData;
	}
	/**
	 * Empties the KR
	 * 
	 * @exception com.logicacmg.koa.exception.KOAException
	 */
	public void emptyKR() throws com.logicacmg.koa.exception.KOAException
	{
		try
		{
			DBUtils xDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(JNDIProperties.DATASOURCE_ESB));
			if (xDBUtils.executeQuery(EMPTY_KR_FINGERPRINT_SQL) < 1)
			{
				throw new KOAException(ErrorConstants.KR_ERROR);
			}
		}
		catch (com.logicacmg.koa.exception.KOADBException xKOADBExc)
		{
			KOALogHelper.logErrorCode(
				"KRSessionEJBBean",
				ErrorConstants.ERR_EMPTY_KR,
				xKOADBExc);
			throw new KOAException(ErrorConstants.KR_ERROR);
		}
	}
}
