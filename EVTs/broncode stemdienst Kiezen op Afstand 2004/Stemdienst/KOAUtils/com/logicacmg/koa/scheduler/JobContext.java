/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.JobContext.java
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
  *  0.1		25-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Properties;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.scheduler.XMLProperties;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The JobContext provides data to the Job it belongs to.
 * It is the 'environment' the job is executed in.
 * 
 * @author KuijerM
 */
public class JobContext
{
	private XMLProperties xmlProps = null;
	private String message = null;
	public JobContext()
	{
		this(null);
	}
	/**
	 * Initialize the context with its properties
	 * 
	 * @param xmlString containing the properties
	 */
	public JobContext(String xmlString)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[JobContext] constructor JobContext");
		/* create new XMLProperties with empty Properties */
		Properties props = new Properties();
		xmlProps = new XMLProperties(props);
		/* fill the XMLProperties */
		try
		{
			if ((xmlString != null) && (!xmlString.trim().equals("")))
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[JobContext] setting xml context: " + xmlString);
				xmlProps.loadXMLString(xmlString);
			}
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"JobContext",
				ErrorConstants.ERR_SCHEDULER_JOBCONTEXT,
				e);
		}
	}
	/**
	 * Get all the properties of this jobcontext in an XML string
	 * 
	 * @return String with the XML content
	 */
	public String getXMLString()
	{
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		/* create XML from XMLProperties */
		try
		{
			xmlProps.storeXML(baos, "JobContext data", "JobContextData");
			return baos.toString();
		}
		catch (IOException ioe)
		{
			String[] params = { "XML props" };
			KOALogHelper.logErrorCode(
				"JobContext.getXMLString",
				ErrorConstants.ERR_IO,
				params,
				ioe);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"JobContext.getXMLString",
				ErrorConstants.ERR_SCHEDULER_JOBCONTEXT,
				e);
		}
		return null;
	}
	/**
	 * Set a property for this jobcontext
	 * 
	 * @param key	the property name to set the value
	 * 
	 * @param value	and its value
	 */
	public void setProperty(String key, String value)
	{
		xmlProps.setProperty(key, value);
	}
	/**
	 * Get the value of a property
	 * 
	 * @param key	the property name to get the value from
	 * 
	 * @return String the value
	 */
	public String getProperty(String key)
	{
		return xmlProps.getProperty(key);
	}
	/**
	 * Set the message of this jobcontext
	 * 
	 * @param message the string containing the message to set
	 */
	public void setMessage(String message)
	{
		this.message = message;
	}
	/**
	 * Get the message of this jobcontext
	 * 
	 * @return String the message to get
	 */
	public String getMessage()
	{
		return message;
	}
}