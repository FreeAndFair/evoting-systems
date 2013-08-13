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
 * Event that represents the status message:<br>
 * 
 * <pre>
 * (status node-id (supervisor|votebox))
 * </pre>
 * 
 * See <a href="https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages">
 * https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages</a> for a complete
 * list of messages.
 * 
 * @author cshaw
 */
public class StatusEvent implements IAnnounceEvent {

    private int serial;

    private int node;

    private IAnnounceEvent status;

    /**
     * Matcher for the StatusEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "status" ), StringWildcard.SINGLETON,
                new ListWildcard( Wildcard.SINGLETON ) );

        private VoteBoxEventMatcher statusMatcher = new VoteBoxEventMatcher(
                SupervisorEvent.getMatcher(), VoteBoxEvent.getMatcher() );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                int node = Integer.parseInt( ((ListExpression) res).get( 0 )
                        .toString() );
                IAnnounceEvent status = statusMatcher.match( 0,
                    ((ListExpression) res).get( 1 ) );
                if (status == null)
                    return null;
                return new StatusEvent( serial, node, status );
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
     * Constructs a new StatusEvent with given serial number, node, and status
     * 
     * @param serial
     *            the serial number
     * @param node
     *            the node
     * @param status
     *            the status
     */
    public StatusEvent(int serial, int node, IAnnounceEvent status) {
        this.serial = serial;
        this.node = node;
        this.status = status;
    }

    /**
     * @return the node
     */
    public int getNode() {
        return node;
    }

    public int getSerial() {
        return serial;
    }

    /**
     * @return the statuses
     */
    public IAnnounceEvent getStatus() {
        return status;
    }

    public void fire(VoteBoxEventListener l) {
        throw new UnsupportedOperationException();
    }

    public ASExpression toSExp() {
        return new ListExpression( StringExpression.makeString( "status" ),
                StringExpression.makeString( Integer.toString( node ) ), status
                        .toSExp() );
    }

}
