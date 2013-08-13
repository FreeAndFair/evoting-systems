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
 * Class used to indicate that the previously committed ballot (corresponding to a nonce) is not
 * being challeneged, and should instead be tallied.
 * 
 * @author Montrose
 *
 */
public class CastCommittedBallotEvent extends CastBallotEvent {

	private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = ASExpression
                .make("(cast-committed-ballot %nonce:#string)");

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            HashMap<String, ASExpression> result = pattern.namedMatch(sexp);
            if (result != NamedNoMatch.SINGLETON)
                return new CastCommittedBallotEvent(serial, result.get("nonce"));

            return null;
        };
    };
	
    /**
     * 
     * @return a MatcherRule for use in identifying and/or parsing this event.
     */
    public static MatcherRule getMatcher(){
    	return MATCHER;
    }
    
    /**
     * Creates a new CastCommittedBallotEvent
     * 
     * @param serial - Serial number of the machine sending the message
     * @param nonce - Nonce of the voting transaction in question.
     */
	public CastCommittedBallotEvent(int serial, ASExpression nonce) {
		super(serial, nonce, StringExpression.EMPTY);
	}
	
	/**
     * @see votebox.events.IAnnounceEvent#toSExp()
     */
	@Override
    public ASExpression toSExp() {
        return new ListExpression(StringExpression.makeString("cast-committed-ballot"),
                getNonce());
    }

}
