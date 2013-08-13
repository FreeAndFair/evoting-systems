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

import sexpression.*;

/**
 * This event represents what gets sent out on the network when the machine
 * needs to commit to a cipher representation of the ballot.<br>
 * <br>
 * Format: (commit-ballot [nonce] [ballot])
 * 
 * @author kyle
 * 
 */
public class CommitBallotEvent implements IAnnounceEvent {

    private final int _serial;
    private final ASExpression _nonce;
    private final ASExpression _ballot;

    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = ASExpression
                .make("(commit-ballot %nonce:#string %ballot:#any)");

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            HashMap<String, ASExpression> result = pattern.namedMatch(sexp);
            if (result != NamedNoMatch.SINGLETON)
                return new CommitBallotEvent(serial, result.get("nonce"), result
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
    
    public CommitBallotEvent(int serial, ASExpression nonce, ASExpression ballot) {
        _serial = serial;
        _nonce = nonce;
        _ballot = ballot;
    }

    public ASExpression getNonce(){
    	return _nonce;
    }
    
    public ASExpression getBallot(){
    	return _ballot;
    }
    
    /**
     * @see votebox.events.IAnnounceEvent#fire(votebox.events.VoteBoxEventListener)
     */
    public void fire(VoteBoxEventListener l) {
        l.commitBallot(this);
    }

    /**
     * @see votebox.events.IAnnounceEvent#getSerial()
     */
    public int getSerial() {
        return _serial;
    }

    /**
     * @see votebox.events.IAnnounceEvent#toSExp()
     */
    public ASExpression toSExp() {
        return new ListExpression(StringExpression.make("commit-ballot"),
                _nonce, _ballot);
    }

}
