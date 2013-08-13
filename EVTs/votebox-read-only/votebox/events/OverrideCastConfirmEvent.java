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

import sexpression.*;

/**
 * Event that represents the override-cast-confirm message:<br>
 * 
 * <pre>
 * (override-cast-confirm nonce encrypted-ballot)
 * </pre>
 * 
 * See <a href="https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages">
 * https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages</a> for a complete
 * list of messages.
 * 
 * @author cshaw
 */
public class OverrideCastConfirmEvent implements IAnnounceEvent {

    private int serial;

    private byte[] nonce;

    private byte[] ballot;

    /**
     * Matcher for the OverrideCastConfirmEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "override-cast-confirm" ),
                StringWildcard.SINGLETON, StringWildcard.SINGLETON );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                /*byte[] nonce = ((StringExpression) ((ListExpression) res)
                        .get( 0 )).getBytesCopy();*/
            	byte[] nonce = new BigInteger(((StringExpression) ((ListExpression) res)
                        .get( 0 )).toString()).toByteArray();
                byte[] ballot = ((StringExpression) ((ListExpression) res)
                        .get( 1 )).getBytesCopy();
                return new OverrideCastConfirmEvent( serial, nonce, ballot );
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
    
    /**
     * Constructs a new OverrideCastConfirmEvent
     * 
     * @param serial
     *            the serial number of the sender
     * @param nonce
     *            the nonce
     * @param ballot
     *            the encrypted ballot
     */
    public OverrideCastConfirmEvent(int serial, byte[] nonce, byte[] ballot) {
        this.serial = serial;
        this.nonce = nonce;
        this.ballot = ballot;
    }

    /**
     * @return the encrypted ballot
     */
    public byte[] getBallot() {
        return ballot;
    }

    /**
     * @return the nonce
     */
    public byte[] getNonce() {
        return nonce;
    }

    public int getSerial() {
        return serial;
    }

    public void fire(VoteBoxEventListener l) {
        l.overrideCastConfirm( this );
    }

    public ASExpression toSExp() {
        /*return new ListExpression( StringExpression
                .makeString( "override-cast-confirm" ), StringExpression
                .makeString( nonce ), StringExpression.makeString( ballot ) );*/
    	return new ListExpression( StringExpression
                .makeString( "override-cast-confirm" ), StringExpression
                .makeString( new BigInteger(nonce).toString() ), StringExpression.makeString( ballot ) );
    }

}
