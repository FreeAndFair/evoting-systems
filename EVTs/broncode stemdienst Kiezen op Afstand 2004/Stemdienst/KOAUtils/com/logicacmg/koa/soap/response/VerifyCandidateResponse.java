/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.VerifyCandidateResponse.java
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
  *  0.1		29-04-2003	XUi 		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.soap.response;
/**
 * Response object after verification of a candidate.
 * 
 * @author Uiterlix
 * 
 */
public class VerifyCandidateResponse implements java.io.Serializable
{
	public int returncode;
	/**
	 * Constructor for the verifyCandidate Response object.
	 * 
	 */
	public VerifyCandidateResponse()
	{
		returncode = -2;
	}
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