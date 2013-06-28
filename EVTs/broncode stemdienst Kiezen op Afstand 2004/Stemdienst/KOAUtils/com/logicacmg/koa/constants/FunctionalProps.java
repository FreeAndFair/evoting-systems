/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.FunctionalProps.java
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
  *  0.1		18-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.constants;
import java.io.IOException;
import java.util.Properties;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The functional properties for KOA
 * 
 * @author MRo
 */
public class FunctionalProps
{
	/**
	 * The singleton instance of the JNDIProperties class
	 */
	private static FunctionalProps g_instance = null;
	/**
	 * The location of the resource to load.
	 * The resource it is looking for is /functional.properties
	 */
	private final static String RESOURCE = "/functional.properties";
	/**
	 * The properties object containing all the propeties
	 */
	private Properties g_pProps = null;
	/**
	 * The string representing the start date and/or time
	 * of the voting proces.
	 */
	public final static String VOTING_START_DATE_TIME =
		"VOTING_START_DATE_TIME";
	/**
	 * The string representing the end date and/or time
	 * of the voting proces.
	 */
	public final static String VOTING_END_DATE_TIME = "VOTING_END_DATE_TIME";
	/**
	 * Show the user a transactioncode or not.
	 * Valid values are:
	 * YES
	 * NO
	 */
	public final static String SHOW_TRANSACTIONCODE = "SHOW_TRANSACTIONCODE";
	/**
	 * number of kandaatcode generated for a lijstpositie
	 * The key value KANDIDAAT_CODE_NUMBER
	 */
	public final static String KANDIDAAT_CODE_NUMBER = "KANDIDAAT_CODE_NUMBER";
	/**
	 * The time in minutes before the account is unlocked after the last valid login attempt
	 * The key value LOGIN_TIME_TO_UNLOCK
	 */
	public final static String LOGIN_TIME_TO_UNLOCK = "LOGIN_TIME_TO_UNLOCK";
	/**
	 * The number of times a person can try to login
	 * The key value LOGIN_NR_TIMES_LOGIN
	 */
	public final static String LOGIN_NR_TIMES_LOGIN = "LOGIN_NR_TIMES_LOGIN";
	/**
	 * The number of times a person can try to login
	 * before this fact is logged
	 */
	public final static String INVALID_NR_LOGIN_LOG = "INVALID_NR_LOGIN_LOG";
	/**
	 * The key for the value for the representation of the 
	 * voting office.
	 * The key value is VOTE_OFFICE
	 */
	public final static String VOTING_OFFICE = "VOTE_OFFICE";
	/**
	 * The string giving a description of the elections
	 * The key value is ELECTION_DESCRIPTION
	 */
	public final static String ELECTION_DESCRIPTION = "ELECTION_DESCRIPTION";
	/**
	 * The string giving a description of the elections
	 * The key value is VOORZITTER
	 */
	public final static String VOORZITTER = "VOORZITTER";
	/**
	 * The string indicating the number of max. attempts that a kiezer is allowed to login
	 * The key value is LOGIN_ATTEMPTS_COUNT
	 */
	public final static String LOGIN_ATTEMPTS_COUNT = "LOGIN_ATTEMPTS_COUNT";
	/**
	 * The string indicating the number of max. attempts that a kiezer
	 * is allowed to try to verify a candidate.
	 */
	public final static String VERIFY_CANDIDATE_ATTEMPTS_COUNT =
		"VERIFY_CANDIDATE_ATTEMPTS_COUNT";
	/**
	 * Strings indicating user friendly text for the source
	 */
	public final static String SOURCE_WEB = "SOURCE_WEB";
	public final static String SOURCE_TEL = "SOURCE_TEL";
	/**
	 * Identifiers to store the reports with (OR 22.3.70)
	 */
	public final static String VW_ADD_KIEZERS = "VW_A_KR";
	public final static String VW_REMOVE_KIEZERS = "VW_D_KR";
	public final static String VW_REPLACE_KIEZERS = "VW_R_KR";
	public final static String VW_REPLACE_KANDIDATENLIJST = "VW_KL";
	public final static String EXPORT_KANDIDATENLIJST = "EX_KL";
	public final static String EXPORT_KIEZERSREGISTER = "EX_KR";
	public final static String WRONGIDS_KANDIDATENLIJST = "WI_KL";
	public final static String WRONGIDS_KIEZERS = "WI_KR";
	/**
	 * Check on action before processing import
	 */
	public final static String IMPORT_DELETE = "DELETE";
	public final static String IMPORT_APPEND = "APPEND";
	public final static String IMPORT_REPLACE = "REPLACE";
	/**
	 * Indicator and text for blank votes
	 */
	public final static String BLANK_VOTE_INDICATOR = "BLANK_VOTE_INDICATOR";
	public final static String BLANK_VOTE_TEXT = "BLANK_VOTE_TEXT";
	public final static String BLANK_VOTE_REPORT_LABEL =
		"BLANK_VOTE_REPORT_LABEL";
	public final static String BLANK_VOTE_REPORT_HEADER =
		"BLANK_VOTE_REPORT_HEADER";
	/**
	 * The private constructor for the FunctionalProps
	 * This method is private to ensure the singleton usage
	 * 
	 * @throws KOAException when the loading of the resource is failing
	 * 
	 */
	private FunctionalProps() throws KOAException
	{
		/* load the properties file */
		this.loadResource();
	}
	/**
	 * Private method to get the instance, to make sure 
	 * there will be only one FunctionalProps instance
	 * 
	 * @return FunctionalProps the instance of the properties object
	 * 
	 * @throws KOAException when anything goes wrong during the get instance
	 * 
	 */
	private static FunctionalProps getInstance() throws KOAException
	{
		/* check if there is an instance */
		if (g_instance == null)
		{
			/* create a new instance */
			g_instance = new FunctionalProps();
		}
		/* return the instance */
		return g_instance;
	}
	/**
	 * load the resource from the file system
	 * 
	 * @throws KOAException when anything goes wrong during the load of the resource
	 * 
	 */
	private void loadResource() throws KOAException
	{
		/* create new properties instance */
		g_pProps = new Properties();
		try
		{
			/* load the resource */
			g_pProps.load(this.getClass().getResourceAsStream(RESOURCE));
		}
		/* catch any io exceptions */
		catch (IOException ioe)
		{
			/* log the error and throw new KOAException */
			String[] params = { "File System " + RESOURCE };
			KOALogHelper.logErrorCode(
				"FunctionalProperties.loadResource",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.FUNC_PROPS_LOAD, ioe);
		}
	}
	/**
	 * Get the property for the specified key
	 * 
	 * @param sKey The key to get the value for
	 * 
	 * @return String the value for the specified key
	 * 
	 * @throws KOAException when the property is not found
	 */
	public synchronized static String getProperty(String sKey)
		throws KOAException
	{
		String sValue = null;
		if (getInstance().g_pProps.containsKey(sKey))
		{
			sValue = getInstance().g_pProps.getProperty(sKey);
		}
		else
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[FunctionalProps.getProperty] Could not found property "
					+ sKey);
			throw new KOAException(ErrorConstants.FUNC_PROPS_NOT_FOUND);
		}
		return sValue;
	}
	/**
	 * Get the property for the specified key
	 * 
	 * @param sKey The key to get the value for
	 * 
	 * @return String the value for the specified key
	 * 
	 * @throws KOAException when the property is not found
	 */
	public synchronized static int getIntProperty(String sKey)
		throws KOAException
	{
		try
		{
			return Integer.parseInt(getProperty(sKey));
		}
		catch (NumberFormatException pe)
		{
			throw new KOAException(ErrorConstants.PROPS_NO_INTEGER, pe);
		}
	}
}