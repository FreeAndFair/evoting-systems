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

import sexpression.*;

/**
 * This is the event that happens when the voter requests 
 * to challenge his vote.
 * 
 * format: (challenge [nonce] [list-of-race-random pairs])
 * 
 * @author sgm2
 * 
 */
public class ChallengeEvent implements IAnnounceEvent {

    private final int _serial;
    private final ASExpression _nonce;
    private final ASExpression _list;

    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "challenge" ), StringWildcard.SINGLETON,
                new ListWildcard(new ListWildcard(StringWildcard.SINGLETON)));

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                StringExpression nonce = ((StringExpression) ((ListExpression) res)
                        .get( 0 ));
                ListExpression list = (ListExpression) ((ListExpression) res).get(1);
                return new ChallengeEvent( serial, nonce,  list);
            }
            return null;
        };
    };
    
    /**
     * 
     * @return a MatcherRule for parsing this type of event.
     */
    public static MatcherRule getMatcher(){
    	return MATCHER;
    }//getMatcher
    
    public ChallengeEvent(int serial, ASExpression nonce,
            ASExpression list) {
        _serial = serial;
        _nonce = nonce;
        _list = list;
    }

    public void fire(VoteBoxEventListener l) {
        l.challenge(this);
    }

    public int getSerial() {
        return _serial;
    }

    public ASExpression getRandom(){
    	return _list;
    }//getRandom
    
    public ASExpression getNonce(){
    	return _nonce;
    }//getNonce
    
    public ASExpression toSExp() {
        return new ListExpression(StringExpression
                .makeString("challenge"), _nonce, _list);
    }

}
