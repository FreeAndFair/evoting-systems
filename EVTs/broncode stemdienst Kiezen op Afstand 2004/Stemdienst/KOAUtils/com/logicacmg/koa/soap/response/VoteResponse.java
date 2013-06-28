/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.VoteResponse.java
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
import com.logicacmg.koa.soap.response.VotingDetails;
/**
 * Response after voting
 * 
 * @author Uiterlix
 * 
 */
public class VoteResponse implements java.io.Serializable
{
	public VotingDetails votingDetails = null;
	public int returncode;
	public int timeToUnlock;
	public VoteResponse()
	{
		returncode = -2;
		votingDetails = new VotingDetails();
		timeToUnlock = 0;
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
	/**
	 * Gets the votingDetails
	 * 
	 * @return VotingDetails
	 */
	public VotingDetails getVotingDetails()
	{
		return votingDetails;
	}
	/**
	 * Sets the votingDetails
	 * 
	 * @param votingDetails The votingDetails to set
	 */
	public void setVotingDetails(VotingDetails votingDetails)
	{
		this.votingDetails = votingDetails;
	}
	/**
	 * Gets the timeToUnlock
	 * 
	 * @return int
	 */
	public int getTimeToUnlock()
	{
		return timeToUnlock;
	}
	/**
	 * Sets the timeToUnlock
	 * 
	 * @param timeToUnlock The timeToUnlock to set
	 */
	public void setTimeToUnlock(int timeToUnlock)
	{
		this.timeToUnlock = timeToUnlock;
	}
}