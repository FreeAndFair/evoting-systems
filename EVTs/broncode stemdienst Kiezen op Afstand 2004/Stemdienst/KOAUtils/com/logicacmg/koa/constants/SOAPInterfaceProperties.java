/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.SOAPInterfaceProperties.java
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
  *  0.1		09-05-2003	XUi			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.constants;
import java.io.IOException;
import java.util.Properties;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
public class SOAPInterfaceProperties
{
	/**
	 * The singleton instance of the SOAPInterfaceProperties class
	 * 
	 */
	private static SOAPInterfaceProperties g_instance = null;
	/**
	 * The properties object containing all the properties
	 * 
	 */
	private Properties g_pProps = null;
	/**
	 * The location of the resource to load.
	 * The resource it is looking for is /soapinterface.properties
	 * 
	 */
	private static final String RESOURCE = "/soapinterface.properties";
	/**
	 * The relative URL of the TSM Webservice
	 */
	public static final String TSM_URL = "tsm.url";
	/**
	 * The namespace the TSM uses for it's webservice
	 */
	public static final String TSM_NAMESPACE = "tsm.namespace";
	/**
	 * The port the TSM webservice listens on
	 */
	public static final String TSM_PORT = "tsm.port";
	/**
	 * The time before a connection the TSM times out
	 */
	public static final String TSM_TIMEOUT = "tsm.timeout";
	/**
	 * The private constructor for the SOAPInterfaceProperties properties
	 * This method is private to ensure the singleton usage
	 * 
	 * @throws KOAException when the loading of the resource is failing
	 * 
	 */
	private SOAPInterfaceProperties() throws KOAException
	{
		/* load the properties file */
		this.loadResource();
	}
	/**
	 * Private method to get the instance, to make sure 
	 * there will be only one SOAPInterfaceProperties instance
	 * 
	 * @return JNDIProperties the instance of the properties object
	 * 
	 * @throws KOAException when anything goes wrong during the get instance
	 * 
	 */
	private static SOAPInterfaceProperties getInstance() throws KOAException
	{
		/* check if there is an instance */
		if (g_instance == null)
		{
			/* create a new instance */
			g_instance = new SOAPInterfaceProperties();
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
				"SOAPInterfaceProperties.loadResource",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.JNDI_PROPS_LOAD, ioe);
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
				"[SOAPInterfaceProperties.getProperty] Could not find property "
					+ sKey);
			throw new KOAException(ErrorConstants.JNDI_PROPS_NOT_FOUND);
		}
		return sValue;
	}
	/**
	 * Get the value for the specified key (doesn't throw exceptions, is used for counter key mapping 
	 * 
	 * @param sKey The key to get the value for
	 * 
	 * @return String the value for the specified key
	 */
	public synchronized static String getNullableProperty(String sKey)
		throws KOAException
	{
		String sValue = null;
		if (getInstance().g_pProps.containsKey(sKey))
		{
			sValue = getInstance().g_pProps.getProperty(sKey);
		}
		return sValue;
	}
}