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
 * This is the event that happens as a response to a voter's challenge. It
 * essentially reveals the randomness values used in elgamal encryption.<br>
 * <br>
 * 
 * format: (challenge-response [nonce] [list-of-r-values])
 * 
 * @author kyle
 * 
 */
public class ChallengeResponseEvent implements IAnnounceEvent {

    private final int _serial;
    private final int _node;
    private final ASExpression _nonce;

    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "challenge-response" ), StringWildcard.SINGLETON,
                StringWildcard.SINGLETON);

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
            	int node = Integer.parseInt( ((ListExpression) res).get( 0 )
                        .toString() );
                StringExpression nonce = ((StringExpression) ((ListExpression) res)
                        .get( 1 ));
                return new ChallengeResponseEvent( serial, node, nonce);
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
    
    public ChallengeResponseEvent(int serial, int node, ASExpression nonce) {
        _serial = serial;
        _node = node;
        _nonce = nonce;
    }

    public void fire(VoteBoxEventListener l) {
        l.challengeResponse(this);
    }

    public int getSerial() {
        return _serial;
    }
    
    public int getNode() {
    	return _node;
    }

    public ASExpression getNonce(){
    	return _nonce;
    }//getNonce
    
    public ASExpression toSExp() {
        return new ListExpression(StringExpression
                .makeString("challenge-response"), StringExpression
                .makeString( Integer.toString( _node ) ), _nonce);
    }

}
