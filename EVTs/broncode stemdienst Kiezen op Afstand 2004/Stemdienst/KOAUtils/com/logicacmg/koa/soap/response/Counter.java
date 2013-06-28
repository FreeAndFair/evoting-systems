/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.Counter.java
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
package com.logicacmg.koa.soap.response;
/**
 * Counter class representing a single key / value pair 
 * for the statistics
 * 
 * @author X@nder
 */
public class Counter
{
	private String key = null;
	private String value = null;
	/**
	 * Constructor for the counter
	 * 
	 */
	public Counter()
	{
		key = "";
		value = "";
	}
	/**
	 * Returns the key of the counter
	 * 
	 * @return String the key of the counter
	 */
	public String getKey()
	{
		return key;
	}
	/**
	 * Returns the value of the counter
	 * 
	 * @return String counter value
	 */
	public String getValue()
	{
		return value;
	}
	/**
	 * Sets the key of the counter
	 * 
	 * @param string The key of the counter
	 */
	public void setKey(String string)
	{
		key = string;
	}
	/**
	 * Sets the value of the counter
	 * 
	 * @param string The value of the counter
	 */
	public void setValue(String string)
	{
		value = string;
	}
}