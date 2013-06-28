/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.PrepareForOpeningResponse.java
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
 * Class representing the response of the TSM
 * for state change prepare for opening.
 * 
 * @author uiterlix
 */
public class PrepareForOpeningResponse
{
	private int returncode;
	private String errormessage = null;
	/**
	 * Returns the error message
	 * 
	 * @return String the error message
	 */
	public String getErrormessage()
	{
		return errormessage;
	}
	/**
	 * Returns the return code
	 * 
	 * @return int The return code
	 */
	public int getReturncode()
	{
		return returncode;
	}
	/**
	 * Sets the error message
	 * 
	 * @param string The error message
	 */
	public void setErrormessage(String string)
	{
		errormessage = string;
	}
	/**
	 * Sets the return code
	 * 
	 * @param i The return code
	 */
	public void setReturncode(int i)
	{
		returncode = i;
	}
}