/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.VerifyVoterResponse.java
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
 * Response object for verification of the voter
 * 
 * @author Uiterlix
 */
public class VerifyVoterResponse implements java.io.Serializable
{
	private VotingDetails votingDetails = null;
	private String ballotID = null;
	private int returncode;
	private int timeToUnlock;
	/**
	 * Constructor setting the default values
	 */
	public VerifyVoterResponse()
	{
		returncode = -2;
		votingDetails = new VotingDetails();
		ballotID = "";
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
	 * Gets the ballotID
	 * @return String
	 */
	public String getBallotID()
	{
		return ballotID;
	}
	/**
	 * Sets the ballotID
	 * 
	 * @param ballotID The ballotID to set
	 */
	public void setBallotID(String ballotID)
	{
		this.ballotID = ballotID;
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