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
 * Event that represents the authorized-to-cast message:<br>
 * 
 * <pre>
 * (authorized-to-cast node-id nonce ballot)
 * </pre>
 * 
 * See <a href="https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages">
 * https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages</a> for a complete
 * list of messages.
 * 
 * @author cshaw
 */
public class AuthorizedToCastEvent implements IAnnounceEvent {

    private int serial;

    private int node;

    private byte[] nonce;

    private byte[] ballot;

    /**
     * The matcher for the AuthorizedToCastEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "authorized-to-cast" ), StringWildcard.SINGLETON,
                StringWildcard.SINGLETON, StringWildcard.SINGLETON );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                int node = Integer.parseInt( ((ListExpression) res).get( 0 )
                        .toString() );
                /*byte[] nonce = ((StringExpression) ((ListExpression) res)
                        .get( 1 )).getBytesCopy();*/
                byte[] nonce = new BigInteger(((StringExpression) ((ListExpression) res)
                        .get( 1 )).toString()).toByteArray();
                byte[] ballot = ((StringExpression) ((ListExpression) res)
                        .get( 2 )).getBytesCopy();
                return new AuthorizedToCastEvent( serial, node, nonce, ballot );
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
     * Constructs a new AuthorizedToCastEvent.
     * 
     * @param serial
     *            the serial number of the sender
     * @param node
     *            the node id
     * @param nonce
     *            the nonce (or authorization code), an array of bytes
     * @param ballot
     *            the ballot in zip format, stored as an array of bytes
     */
    public AuthorizedToCastEvent(int serial, int node, byte[] nonce,
            byte[] ballot) {
        this.serial = serial;
        this.node = node;
        this.nonce = nonce;
        this.ballot = ballot;
    }

    /**
     * @return the ballot
     */
    public byte[] getBallot() {
        return ballot;
    }

    /**
     * @return the node
     */
    public int getNode() {
        return node;
    }

    /**
     * @return the nonce, or authorization code
     */
    public byte[] getNonce() {
        return nonce;
    }

    public int getSerial() {
        return serial;
    }

    public void fire(VoteBoxEventListener l) {
        l.authorizedToCast( this );
    }

    public ASExpression toSExp() {
        /*return new ListExpression( StringExpression
                .makeString( "authorized-to-cast" ), StringExpression
                .makeString( Integer.toString( node ) ), StringExpression
                .makeString( nonce ), StringExpression.makeString( ballot ) );*/
    	return new ListExpression( StringExpression
                .makeString( "authorized-to-cast" ), StringExpression
                .makeString( Integer.toString( node ) ), StringExpression
                .makeString( new BigInteger(nonce).toString() ), StringExpression.makeString( ballot ) );
    }
    
}
