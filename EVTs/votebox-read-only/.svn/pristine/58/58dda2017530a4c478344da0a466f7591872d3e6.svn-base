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

import java.math.BigInteger;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.NoMatch;
import sexpression.StringExpression;
import sexpression.StringWildcard;

public class BallotCountedEvent extends BallotReceivedEvent{

	public BallotCountedEvent(int serial, int node, byte[] nonce) {
		super(serial, node, nonce);
	}
	
	/**
     * The matcher for the BallotReceivedEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "ballot-counted" ), StringWildcard.SINGLETON,
                StringWildcard.SINGLETON );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                int node = Integer.parseInt( ((ListExpression) res).get( 0 )
                        .toString() );
                /*byte[] nonce = ((StringExpression) ((ListExpression) res)
                        .get( 1 )).getBytesCopy();*/
                byte[] nonce = new BigInteger(((StringExpression) ((ListExpression) res)
                        .get( 1 )).toString()).toByteArray();
                return new BallotCountedEvent( serial, node, nonce );
            }
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
    
    @Override
    public void fire(VoteBoxEventListener l) {
        l.ballotCounted( this );
    }

    public ASExpression toSExp() {
        /*return new ListExpression( StringExpression
                .makeString( "ballot-counted" ), StringExpression
                .makeString( Integer.toString( getNode() ) ), StringExpression
                .makeString( getNonce() ) );*/
    	
    	return new ListExpression( StringExpression
                .makeString( "ballot-counted" ), StringExpression
                .makeString( Integer.toString( getNode() ) ), StringExpression
                .makeString( new BigInteger(getNonce()).toString() ) );
    }
    
}
