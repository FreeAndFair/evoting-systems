/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.StemTransactie.java
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
  *  0.1		17-04-2003	Agr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.util.Date;

import com.logicacmg.koa.dataobjects.Kiezer;
/**
 * This class contains data about the result of a vote transaction
 */
public class StemTransactie implements java.io.Serializable
{
	//VoteStatus constants
	//kiezer doesn't exists
	public final static int KIEZER_DELETED = -3;
	//voting failed
	public final static int VOTING_FAILED = -2;
	// the election isn't open yet, so prepare or initialized
	public final static int ELECTION_NOT_YET_OPEN = -1;
	// the elections are already closed, so closed, ready to count or votes counted
	public final static int ELECTION_CLOSED = -4;
	// vote transactio is OK
	public final static int OK = 0;
	//credentials of the kiezer are invalid
	public final static int INVALID_CREDENTIALS = 1;
	//the account of the kiezer is locked
	public final static int ACCOUNT_LOCKED = 2;
	// the kiezer has already voted
	public final static int ALREADY_VOTED = 3;
	//the candidate choosen by the kiezer doesn't exist
	public final static int INVALID_CANDIDATE = 4;
	//the election is suspended
	public final static int ELECTION_SUSPENDED = 5;
	//election is blocked
	public final static int ELECTION_BLOCKED = 6;
	// stemcode only consists of digits
	public final static int NON_NUMERIC_CODE = 7;
	// stemcode only consists of 9 digits
	public final static int NINE_DIGITS = 8;
	//transactionnumber when a vote is succesfully proceeded
	public String Transactienummer;
	//the time of the voting
	public Date VotingTime;
	//the channel (modaliteit) of the of which the vote has come in
	public String Modaliteit;
	//the status of the vote
	public int VoteStatus;
	public String Stemcode;
	//kiezer object
	public Kiezer kiezer = null;
}
