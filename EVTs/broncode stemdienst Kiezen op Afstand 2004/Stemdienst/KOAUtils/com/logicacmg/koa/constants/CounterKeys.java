/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.CounterKeys.java
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
  *  0.1		11-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.constants;
import java.io.IOException;
import java.util.Properties;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The constant values representing the different
 * types of counter keys available in the KOA system.
 * 
 * @author KuijerM
 * 
 */
public class CounterKeys
{
	/**
	 * The singleton instance of the TechnicalProps class
	 * 
	 */
	private static CounterKeys g_instance = null;
	/**
	 * The properties object containing all the propeties
	 * 
	 */
	private Properties g_pProps = null;
	/**
	 * The location of the resource to load.
	 * The resource it is looking for is /counterkeys.properties
	 * 
	 */
	private final static String RESOURCE = "/counterkeys.properties";
	public static final int STATECHANGE = 0;
	public static final int PERIODIC = 1;
	public static final int COUNTBEFORE = 0;
	public static final int COUNTAFTER = 1;
	public static final String INIT_SCHEDULER = "SCHEDULER";
	/**
	 * Private constructor to prevent 
	 * creating an instance of this class
	 * 
	 */
	private CounterKeys()
	{
		/* load the properties file */
		this.loadResource();
	}
	/**
	 * The identifier for the counter to count the 
	 * requests to vote while the elections are open.
	 * 
	 */
	public static final String OPROEPEN_BEDRIJF = "OPROEPEN_BEDRIJF";
	/**
	 * The identifier for the counter to count the 
	 * requests to vote while the elections are not open.
	 * 
	 */
	public static final String OPROEPEN_BUITEN_BEDRIJF =
		"OPROEPEN_BUITEN_BEDRIJF";
	/**
	 * The identifier for the counter to count the 
	 * number of times the verification of a user 
	 * was succesful.
	 * 
	 */
	public static final String VERIFICATIE_GELUKT = "VERIFICATIE_GELUKT";
	/**
	 * The identifier for the counter to count the 
	 * number of times the verification of a user 
	 * was not succesful.
	 * 
	 */
	public static final String VERIFICATIE_MISLUKT = "VERIFICATIE_MISLUKT";
	/**
	 * The identifier for the counter to count the 
	 * number of votes that are succesfully completed.
	 * 
	 */
	public static final String STEMMEN_UITGEBRACHT = "STEMMEN_UITGEBRACHT";
	/**
	 * The identifier for the counter to count the 
	 * number of times the lines were busy for the TSM.
	 * 
	 */
	public static final String IN_GESPREK = "IN_GESPREK";
	/**
	 * The identifier for the counter to count the 
	 * number of times the call is ended by the voter
	 * before completing the vote for the TSM.
	 * 
	 */
	public static final String AFGEBROKEN = "AFGEBROKEN";
	/**
	 * The identifier for the counter to count the 
	 * number of times accounts are locked.
	 * 
	 */
	public static final String ACCOUNT_LOCK = "ACCOUNT_LOCK";
	/**
	 * Translates the counter key to a dutch discription of the counter.
	 * 
	 * @param sKey The key of the counter to translate
	 * 
	 * @return String the translation of the counter key
	 * 
	 */
	public static String getDutchTranslationForCounter(String sKey)
	{
		if (sKey == null)
		{
			return "Onbekende teller";
		}
		sKey = sKey.trim();
		return getProperty(sKey);
	}
	/**
	 * Private method to get the instance, to make sure 
	 * there will be only one TechnicalProps instance
	 * 
	 * @return TechnicalProps the instance of the properties object
	 * 
	 * @throws KOAException when anything goes wrong during the get instance
	 * 
	 */
	private static CounterKeys getInstance()
	{
		/* check if there is an instance */
		if (g_instance == null)
		{
			/* create a new instance */
			g_instance = new CounterKeys();
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
	private void loadResource()
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
			String[] params = { "Load file " + RESOURCE };
			KOALogHelper.logErrorCode(
				"CounterKeys.loadResource",
				ErrorConstants.ERR_IO,
				params,
				ioe);
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
	{
		String sValue = null;
		if (getInstance().g_pProps != null
			&& getInstance().g_pProps.containsKey(sKey))
		{
			sValue = getInstance().g_pProps.getProperty(sKey);
		}
		else
		{
			return sKey;
		}
		return sValue;
	}
}