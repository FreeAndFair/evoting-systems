/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.SubscribeResponse.java
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
 * Response object for the subscription of the TSM at the VSL.
 * 
 * @author Uiterlix
 */
public class SubscribeResponse implements java.io.Serializable
{
	public int status;
	/**
	 * Gets the status
	 * 
	 * @return int
	 */
	public int getStatus()
	{
		return status;
	}
	/**
	 * Sets the status
	 * 
	 * @param status The status to set
	 */
	public void setStatus(int status)
	{
		this.status = status;
	}
}