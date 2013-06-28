/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.TechnicalProps.java
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
  *  0.1		25-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.constants;
import java.io.IOException;
import java.util.Properties;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The Technical properties for KOA
 * 
 * @author MRo
 */
public class TechnicalProps
{
	/**
	 * The singleton instance of the TechnicalProps class
	 * 
	 */
	private static TechnicalProps g_instance = null;
	/**
	 * The location of the resource to load.
	 * The resource it is looking for is /functional.properties
	 */
	private final static String RESOURCE = "/technical.properties";
	public final static String[] KR_STATIC_COLUMNS =
		{
			"STEMCODE",
			"KIEZERIDENTIFICATIE",
			"HASHEDWACHTWOORD",
			"KIESKRINGNUMMER" /*,"ACCOUNTLOCKED"*/
	};
	public final static String[] KR_DYNAMIC_COLUMNS =
		{
			"REEDSGESTEMD",
			"INVALIDLOGINS",
			"LOGINATTEMPTSLEFT",
			"TIMESTAMPUNLOCK",
			"TIMELASTSUCCESFULLOGIN",
			"ACCOUNTLOCKED",
			"VALIDLOGINS" };
	public final static String KR_SCHEMA_NAME = "KOA01";
	public final static String KR_TABLE_NAME = "KIEZERS";
	public final static String KR_SORT_KEY = "STEMCODE";
	public final static String KIESLIJST_SCHEMA_NAME = "KOA01";
	public final static String KIESLIJST_KANDIDAATCODE_TABLE_NAME =
		"KANDIDAATCODES";
	public final static String[] KIESLIJST_KANDIDAATCODE_COLUMNS =
		{
			"KANDIDAATCODE",
			"KIESKRINGNUMMER",
			"KIESLIJSTNUMMER",
			"POSITIENUMMER" };
	public final static String KIESLIJST_KANDIDAATCODE_SORT_KEY =
		"KANDIDAATCODE";
	public final static String KIESLIJST_LIJSTPOSITIES_TABLE_NAME =
		"LIJSTPOSITIES";
	public final static String[] KIESLIJST_LIJSTPOSITIES_COLUMNS =
		{
			"KIESKRINGNUMMER",
			"KIESLIJSTNUMMER",
			"POSITIENUMMER",
			"ACHTERNAAM",
			"VOORLETTERS",
			"ROEPNAAM",
			"GESLACHT",
			"WOONPLAATS" };
	public final static String KIESLIJST_LIJSTPOSITIES_SORT_KEY =
		"KIESKRINGNUMMER, KIESLIJSTNUMMER, POSITIENUMMER";
	public final static String KIESLIJST_KIESLIJST_TABLE_NAME = "KIESLIJSTEN";
	public final static String[] KIESLIJST_KIESLIJST_COLUMNS =
		{ "KIESKRINGNUMMER", "KIESLIJSTNUMMER", "LIJSTNAAM" };
	public final static String KIESLIJST_KIESLIJST_SORT_KEY =
		"KIESKRINGNUMMER, KIESLIJSTNUMMER";
	/**
	 * The properties object containing all the propeties
	 * 
	 */
	private Properties g_pProps = null;
	/**
	 * Tempory dir for upload files
	 * The key value TEMPDIR_UPLOAD
	 * 
	 */
	public final static String TEMPDIR_UPLOAD = "TEMPDIR_UPLOAD";
	/**
	 * Tempory dir for report files
	 * The key value TEMPDIR_REPORT
	 * 
	 */
	public final static String TEMPDIR_REPORT = "TEMPDIR_REPORT";
	/**
	 * Amount of kiezer in one commit
	 * The key value KIEZER_COMMIT
	 * 
	 */
	public final static String KIEZER_COMMIT = "KIEZER_COMMIT";
	/**
	 * Amount of kiezer deleted in one commit
	 * The key value KIEZER_DELETE
	 * 
	 */
	public final static String KIEZER_DELETE = "KIEZER_DELETE";
	/**
	 * The XML encoding used for the import
	 * The key value XML_ENCODING
	 * 
	 */
	public final static String XML_ENCODING = "XML_ENCODING";
	/**
	 * The location of the FOP configuration file
	 * 
	 */
	public final static String FOP_CONFIG_FILE = "FOP_CONFIG_FILE";
	/**
	 * The transaction timeout for the scheduler
	 * 
	 */
	public final static String SCHEDULE_TX_TIMEOUT = "SCHEDULE_TX_TIMEOUT";
	/**
	 * The XML encoding used for the kieslijst export
	 * The key value KL_EXPORT_XML_ENCODING
	 * 
	 */
	public final static String KL_EXPORT_XML_ENCODING =
		"KL_EXPORT_XML_ENCODING";
	/**
	 * The length in bytes of the RSA key pair
	 * 
	 */
	public final static String RSA_KEY_LENGTH = "RSA_KEY_LENGTH";
	/**
	 * The current application version.
	 * The key value APPL_VERSION
	 * 
	 */
	public final static String APPL_VERSION = "APPL_VERSION";
	/**
	 * Property to indicate if it is an multinode configuration. 
	 * If it is a multinode configuration it is 'true'
	 * if it is not a multinode configuration it is 'false'
	 * 
	 */
	public final static String APPL_MULTI_NODE_CONFIG = "MULTI_NODE_CONFIG";
	/**
	 * Property to indicate if the system is in debug mode
	 * If it is in debugmode it is 'true'
	 * if it is not in debugmode it is 'false'
	 * 
	 */
	public final static String DEBUG_MODE = "DEBUG_MODE";
	/**
	 * Property to indicate how many votes to commit in 1 batch while decrypting
	 * 
	 */
	public final static String DECRYPTEDVOTE_COMMIT = "DECRYPTEDVOTE_COMMIT";
	/**
	 * Property to indicate the maximum number of attempts 
	 * to generate a unique random number
	 */
	public final static String MAX_RANDOM_ATTEMPTS = "MAX_RANDOM_ATTEMPTS";
	/**
	 * Property that gives the path that points to the backup script
	 */
	public final static String BACKUP_SCRIPT = "BACKUP_SCRIPT";
	/**
	 * Property that gives the path that points to the script that backups the db to the filesystem
	 */
	public final static String BACKUP_SCRIPT_FS = "BACKUP_SCRIPT_FS";
	/**
	 * Property that gives the path that points to the script that moves the exported data to tape (i.e. background process !!!)
	 */
	public final static String BACKUP_SCRIPT_TAPE = "BACKUP_SCRIPT_TAPE";
	/**
	 * Property to indicate how many records the BLOBResultSet should
	 * read at once
	 */
	public final static String BLOB_RS_SIZE = "BLOB_RS_SIZE";
	/**
	 * The private constructor for the TechnicalProps
	 * This method is private to ensure the singleton usage
	 * 
	 * @throws KOAException when the loading of the resource is failing
	 * 
	 */
	private TechnicalProps() throws KOAException
	{
		/* load the properties file */
		this.loadResource();
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
	private static TechnicalProps getInstance() throws KOAException
	{
		/* check if there is an instance */
		if (g_instance == null)
		{
			/* create a new instance */
			g_instance = new TechnicalProps();
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
	private synchronized void loadResource() throws KOAException
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
			String[] params = { "Technical Properties" };
			KOALogHelper.logErrorCode(
				"TechnicalProperties.loadResource",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.TECHN_PROPS_LOAD, ioe);
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
	public static String getProperty(String sKey) throws KOAException
	{
		String sValue = null;
		sValue = getInstance().g_pProps.getProperty(sKey);
		if (sValue == null)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[TechnicalProps.getProperty] Could not found property "
					+ sKey);
			throw new KOAException(ErrorConstants.TECHN_PROPS_NOT_FOUND);
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
	public static int getIntProperty(String sKey) throws KOAException
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
	public static boolean isMultiNodeConfiguration()
	{
		boolean isMultiNodeConfig = false;
		try
		{
			String config = getProperty(TechnicalProps.APPL_MULTI_NODE_CONFIG);
			if (config != null)
			{
				config = config.toLowerCase();
				isMultiNodeConfig = config.equals("true");
			}
		}
		catch (Exception e)
		{
			isMultiNodeConfig = false;
		}
		return isMultiNodeConfig;
	}
	public static boolean isDebugMode()
	{
		boolean isDebugMode = false;
		try
		{
			String config = getProperty(TechnicalProps.DEBUG_MODE);
			if (config != null)
			{
				config = config.toLowerCase();
				isDebugMode = config.equals("true");
			}
		}
		catch (Exception e)
		{
			isDebugMode = false;
		}
		return isDebugMode;
	}
}