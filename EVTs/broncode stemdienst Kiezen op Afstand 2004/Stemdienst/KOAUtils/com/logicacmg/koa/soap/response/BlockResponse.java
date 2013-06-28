/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.BlockResponse.java
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
import com.logicacmg.koa.soap.response.Statistics;
/**
 * Response for the block state change
 * 
 * @author uiterlix
 *
 */
public class BlockResponse
{
	private int returncode;
	private String errormessage = null;
	private Statistics statistics = null;
	/**
	 * Returns the error message
	 * 
	 * @return String error Message
	 */
	public String getErrormessage()
	{
		return errormessage;
	}
	/**
	 * Returns the return code
	 * 
	 * @return int return code
	 */
	public int getReturncode()
	{
		return returncode;
	}
	/**
	 * Returns the statistics of the TSM
	 * 
	 * @return Statistics The statistics of the TSM
	 */
	public Statistics getStatistics()
	{
		return statistics;
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
	/**
	 * Sets the statistics of the TSM
	 * 
	 * @param statistics The statistics
	 */
	public void setStatistics(Statistics statistics)
	{
		this.statistics = statistics;
	}
}
