/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package supervisor.model.tallier;

import java.util.HashMap;
import java.util.Map;

import auditorium.Bugout;
import auditorium.Key;

import sexpression.ASExpression;

/**
 * Tallier implementation that caches ballots until a second message (affirming the voter is NOT challenging)
 * is received.  At which point the cached ballot is added to the tally.
 * 
 * @author Montrose
 *
 */
public class ChallengeDelayedTallier extends EncryptedTallier {
	//Mapping of nonce values to pending ballots
	private Map<ASExpression, byte[]> _nonceToBallot = new HashMap<ASExpression, byte[]>();
	
	public ChallengeDelayedTallier(Key privateKey){
		super(privateKey);
	}
	
	@Override
	public void recordVotes(byte[] message, ASExpression nonce){
		_nonceToBallot.put(nonce,message);
	}//recordVotes
	
	public void confirmed(ASExpression nonce){
		byte[] vote = _nonceToBallot.remove(nonce);
		
		if(vote == null){
			throw new RuntimeException("Attempted to confirm an unknown vote, nonce = "
				+ nonce
				+ " -- perhaps the ballot is not designed to use the challenge model?");
		}//if
		
		//Delegate actually tallying to the EncryptedTallier class
		super.recordVotes(vote, null);
	}//confirmed
	
	public void challenged(ASExpression nonce){
		
		//This could be innoculous (supervisor going on and offline)
		//Or it could be a sign of malicious tampering, so we'll report it.
		if(_nonceToBallot.remove(nonce) == null){
			Bugout.err("Detected a challenge on an UNKNOWN vote, nonce  = "+nonce);
		}//if
	}//challenge
}
