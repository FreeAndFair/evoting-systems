/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.request.SOAPRequest.java
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
  *  1.0		29-04-2003	XUi 		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.soap.request;
import java.util.Hashtable;
/**
 * SOAPRequest: Wrapper class analog to the HTTPRequest to make commands SOAP Compatible
 */
public class SOAPRequest
{
	Hashtable parameters = null;
	/**
	 * Constructor Create an empty SOAPRequest
	 */
	public SOAPRequest()
	{
		parameters = new Hashtable();
	}
	/**
	 * Set a parameter
	 * 
	 * @param param The parameter to set
	 * @param value The value for the parameter
	 */
	public void setParameter(String param, Object value)
	{
		parameters.put(param, value);
	}
	/**
	 * Get a parameter
	 * 
	 * @param param The parameter which value to get
	 * 
	 * @return Object	The value of the requested parameter
	 */
	public Object getParameter(String param)
	{
		return parameters.get(param);
	}
}