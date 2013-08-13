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

package votebox.events;

import java.util.HashMap;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.NamedNoMatch;
import sexpression.StringExpression;

/**
 * An event resulting from the receipt of a encrypted-cast-ballot event.<BR>
 * Form:<BR>
 * (encrypted-cast-ballot [nonce] [ballot])<BR>
 * Where [ballot] is in the form ((cand-#1-vote-race1 cand-#2-vote-race1) (cand-#1-vote-race2 ...))
 * with a whole message of E(...) thrown in.
 * @author Montrose
 */
public class EncryptedCastBallotEvent extends CastBallotEvent{
	
    /**
     * Matcher for the EncryptedCastBallotEvent
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = ASExpression
                .make("(encrypted-cast-ballot %nonce:#string %ballot:#any)");

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            HashMap<String, ASExpression> result = pattern.namedMatch(sexp);
            if (result != NamedNoMatch.SINGLETON)
                return new EncryptedCastBallotEvent(serial, result.get("nonce"), result
                        .get("ballot"));

            return null;
        };
    };
	
    /**
     * 
     * @return a MatcherRule for parsing this event type.
     */
    public static MatcherRule getMatcher(){
    	return MATCHER;
    }//getMatcher
    
	/**
     * @param serial
     *            the serial number of the sender
     * @param nonce
     *            the nonce
     * @param ballot
     *            the encrypted ballot, as an array of bytes
     */
    public EncryptedCastBallotEvent(int serial, ASExpression nonce, ASExpression ballot) {
        super(serial, nonce, ballot);
    }

	/**
     * @see votebox.events.IAnnounceEvent#toSExp()
     */
	public ASExpression toSExp() {
		return new ListExpression(StringExpression.makeString("encrypted-cast-ballot"),
                getNonce(), getBallot());
	}
	
}
