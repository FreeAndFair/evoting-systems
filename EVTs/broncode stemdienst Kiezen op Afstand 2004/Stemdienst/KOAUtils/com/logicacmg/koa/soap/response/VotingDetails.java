/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.VotingDetails.java
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
import java.util.Date;
/**
 * Class representing the voting details with more 
 * information about the voting. The information is
 * the transaction code, timestamp of voting and the channel.
 * 
 * @author Uiterlix
 */
public class VotingDetails
{
	public String TX_code = null;
	public Date timestamp_voted = null;
	public int channel;
	public VotingDetails()
	{
		TX_code = "";
		timestamp_voted = new Date();
		channel = -1;
	}
	/**
	 * Gets the tX_code
	 * 
	 * @return String
	 */
	public String getTX_code()
	{
		return TX_code;
	}
	/**
	 * Sets the tX_code
	 * 
	 * @param tX_code The tX_code to set
	 */
	public void setTX_code(String tX_code)
	{
		TX_code = tX_code;
	}
	/**
	 * Gets the timestamp_voted
	 * 
	 * @return Date
	 */
	public Date getTimestamp_voted()
	{
		return timestamp_voted;
	}
	/**
	 * Sets the timestamp_voted
	 * 
	 * @param timestamp_voted The timestamp_voted to set
	 */
	public void setTimestamp_voted(Date timestamp_voted)
	{
		this.timestamp_voted = timestamp_voted;
	}
	/**
	 * Gets the channel
	 * 
	 * @return int
	 */
	public int getChannel()
	{
		return channel;
	}
	/**
	 * Sets the channel
	 * 
	 * @param channel The channel to set
	 */
	public void setChannel(int channel)
	{
		this.channel = channel;
	}
}