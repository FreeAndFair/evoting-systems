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
 * Event that represents the last-polls-open message:<br>
 * 
 * <pre>
 * (last - polls - open( polls - open ))
 * </pre>
 * 
 * See <a href="https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages">
 * https://sys.cs.rice.edu/votebox/trac/wiki/VotingMessages</a> for a complete
 * list of messages.
 * 
 * @author cshaw
 */
public class LastPollsOpenEvent implements IAnnounceEvent {

    private int serial;

    private PollsOpenEvent pollsOpenMsg;

    /**
     * Matcher for the LastPollsOpenEvent.
     */
    private static MatcherRule MATCHER = new MatcherRule() {
        private ASExpression pattern = new ListExpression( StringExpression
                .makeString( "last-polls-open" ), new ListWildcard(
                Wildcard.SINGLETON ) );

        private VoteBoxEventMatcher pollsOpenMatcher = new VoteBoxEventMatcher(
                PollsOpenEvent.getMatcher() );

        public IAnnounceEvent match(int serial, ASExpression sexp) {
            ASExpression res = pattern.match( sexp );
            if (res != NoMatch.SINGLETON) {
                IAnnounceEvent pollsOpenMsg = pollsOpenMatcher.match( 0,
                    ((ListExpression) res).get( 0 ) );
                if (pollsOpenMsg == null)
                    return null;
                return new LastPollsOpenEvent( serial,
                        (PollsOpenEvent) pollsOpenMsg );
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
     * Constructs a new LastPollsOpenEvent.
     * 
     * @param serial
     *            the serial number of the sender
     * @param pollsOpenMsg
     *            a PollsOpenEvent representing the last polls-open message seen
     */
    public LastPollsOpenEvent(int serial, PollsOpenEvent pollsOpenMsg) {
        super();
        this.serial = serial;
        this.pollsOpenMsg = pollsOpenMsg;
    }

    public int getSerial() {
        return serial;
    }

    /**
     * @return the polls open message as an event
     */
    public PollsOpenEvent getPollsOpenMsg() {
        return pollsOpenMsg;
    }

    public void fire(VoteBoxEventListener l) {
        l.lastPollsOpen( this );
    }

    public ASExpression toSExp() {
        return new ListExpression( StringExpression
                .makeString( "last-polls-open" ), pollsOpenMsg.toSExp() );
    }

}
