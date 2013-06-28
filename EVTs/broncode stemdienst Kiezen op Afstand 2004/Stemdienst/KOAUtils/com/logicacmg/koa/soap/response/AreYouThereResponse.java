/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.AreYouThereResponse.java
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
 * The Are you there response for the TSM
 * 
 * @author UiterliX
 */
public class AreYouThereResponse implements java.io.Serializable
{
	public int returncode;
	/**
	 * Gets the returncode
	 * 
	 * @return int
	 */
	public int getReturncode()
	{
		return returncode;
	}
	/**
	 * Sets the returncode
	 * 
	 * @param returncode The returncode to set
	 */
	public void setReturncode(int returncode)
	{
		this.returncode = returncode;
	}
}