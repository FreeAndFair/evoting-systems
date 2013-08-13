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

import sexpression.ASExpression;

/**
 * A VoteBoxEventMatcher contains a list of rules to check messages against, and
 * has a match method that performs this series of checks on the message. This
 * exists in its own class so that messages that contain other messages can have
 * their own VoteBoxEventMatchers that only use the rules of the contained
 * messages.
 * @author cshaw
 */
public class VoteBoxEventMatcher {

    private MatcherRule[] rules;

    /**
     * Constructs a VoteBoxEventMatcher with the given matcher rules
     * @param rules the rules
     */
    public VoteBoxEventMatcher(MatcherRule... rules) {
        this.rules = rules;
    }

    /**
     * Attempts to find a match for the given sexp using this matcher's rules.
     * Upon finding a successful match, the result is returned immediately. No
     * checks are performed to see if a message matches multiple rules; only the
     * first match that was found (in order of passing to the constructor) is
     * used. If the message does not match any of the rules, null is returned.
     * @param serial the serial number of the sender, to use in event
     *            constructors
     * @param sexp the sexpression to attempt matches on
     * @return an event constructed from the expression if a match was found,
     *         null otherwise
     */
    public IAnnounceEvent match(int serial, ASExpression sexp) {
        for (MatcherRule rule : rules) {
            IAnnounceEvent res = rule.match(serial, sexp);
            if (res != null) return res;
        }
        return null;
    }

}
