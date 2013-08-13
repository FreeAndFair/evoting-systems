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

import java.util.ArrayList;
import java.util.List;

import sexpression.*;

/**
 * Event that represents the activated message:<br>
 * 
 * <pre>
 * (activated ((status)*))
 * </pre>
 * 
 * See <a href="https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages">
 * https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages</a> for a complete
 * list of messages.
 * 
 * @author cshaw
 */
public class ActivatedEvent implements IAnnounceEvent {

    private int serial;

    private List<StatusEvent> statuses;

    /**
     * Matcher for the ActivatedEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "activated" ), new ListWildcard( new ListWildcard(
                Wildcard.SINGLETON ) ) );

        private VoteBoxEventMatcher statusMatcher = new VoteBoxEventMatcher(
                StatusEvent.getMatcher() );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                ArrayList<StatusEvent> statuses = new ArrayList<StatusEvent>();
                for (ASExpression s : (ListExpression) ((ListExpression) res)
                        .get( 0 )) {
                    StatusEvent status = (StatusEvent) statusMatcher.match( 0,
                        s );
                    if (status == null)
                        return null;
                    statuses.add( status );
                }
                return new ActivatedEvent( serial, statuses );
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
     * Constructs a new ActivatedEvent with given serial number and list of
     * known statuses
     * 
     * @param serial
     *            the serial number
     * @param statuses
     *            the list of known statuses
     */
    public ActivatedEvent(int serial, List<StatusEvent> statuses) {
        this.serial = serial;
        this.statuses = statuses;
    }

    public int getSerial() {
        return serial;
    }

    /**
     * @return the list of known statuses
     */
    public List<StatusEvent> getStatuses() {
        return statuses;
    }

    public void fire(VoteBoxEventListener l) {
        l.activated( this );
    }

    public ASExpression toSExp() {
        ArrayList<ASExpression> statusList = new ArrayList<ASExpression>();
        for (IAnnounceEvent s : statuses)
            statusList.add( s.toSExp() );
        return new ListExpression( StringExpression.makeString( "activated" ),
                new ListExpression( statusList ) );
    }

}
