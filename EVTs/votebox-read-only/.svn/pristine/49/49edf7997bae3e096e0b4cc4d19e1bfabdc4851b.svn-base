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
 * Event that represents the supervisor message:<br>
 * 
 * <pre>
 * (supervisor local-timestamp supervisor-status)
 * </pre>
 * 
 * See <a href="https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages">
 * https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages</a> for a complete
 * list of messages.
 * 
 * @author cshaw
 */
public class SupervisorEvent implements IAnnounceEvent {

    private int serial;

    private long timestamp;

    private String status;

    /**
     * Matcher for the supervisor message
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "supervisor" ), StringWildcard.SINGLETON,
                StringWildcard.SINGLETON );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                long timestamp = Long.parseLong( ((ListExpression) res).get( 0 )
                        .toString() );
                String status = ((ListExpression) res).get( 1 ).toString();
                return new SupervisorEvent( serial, timestamp, status );
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
     * Constructs a new SupervisorEvent
     * 
     * @param serial
     *            the serial number of the sender
     * @param timestamp
     *            the local timestamp
     * @param status
     *            the supervisor's status
     */
    public SupervisorEvent(int serial, long timestamp, String status) {
        this.serial = serial;
        this.timestamp = timestamp;
        this.status = status;
    }

    public int getSerial() {
        return serial;
    }

    /**
     * @return the status, either "active" or "inactive"
     */
    public String getStatus() {
        return status;
    }

    /**
     * @return the timestamp
     */
    public long getTimestamp() {
        return timestamp;
    }

    public void fire(VoteBoxEventListener l) {
        l.supervisor( this );
    }

    public ASExpression toSExp() {
        return new ListExpression( StringExpression.makeString( "supervisor" ),
                StringExpression.makeString( Long.toString( timestamp ) ),
                StringExpression.makeString( status ) );
    }

}
