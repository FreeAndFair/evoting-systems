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

package votebox.events.test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import junit.framework.TestCase;
import sexpression.ASExpression;
import sexpression.StringExpression;
import votebox.events.ActivatedEvent;
import votebox.events.AssignLabelEvent;
import votebox.events.AuthorizedToCastEvent;
import votebox.events.BallotReceivedEvent;
import votebox.events.CastBallotEvent;
import votebox.events.LastPollsOpenEvent;
import votebox.events.OverrideCancelConfirmEvent;
import votebox.events.OverrideCancelDenyEvent;
import votebox.events.OverrideCancelEvent;
import votebox.events.OverrideCastConfirmEvent;
import votebox.events.OverrideCastDenyEvent;
import votebox.events.OverrideCastEvent;
import votebox.events.PollsClosedEvent;
import votebox.events.PollsOpenEvent;
import votebox.events.StatusEvent;
import votebox.events.SupervisorEvent;
import votebox.events.VoteBoxEvent;
import votebox.events.VoteBoxEventMatcher;

public class VoteBoxEventsTest extends TestCase {

    private VoteBoxEventMatcher matcher;

    protected void setUp() throws Exception {
        super.setUp();
        matcher = new VoteBoxEventMatcher(ActivatedEvent.getMatcher(),
                AssignLabelEvent.getMatcher(), AuthorizedToCastEvent.getMatcher(),
                BallotReceivedEvent.getMatcher(), CastBallotEvent.getMatcher(),
                LastPollsOpenEvent.getMatcher(), OverrideCancelConfirmEvent.getMatcher(),
                OverrideCancelDenyEvent.getMatcher(), OverrideCancelEvent.getMatcher(),
                OverrideCastConfirmEvent.getMatcher(),
                OverrideCastDenyEvent.getMatcher(), OverrideCastEvent.getMatcher(),
                PollsClosedEvent.getMatcher(), PollsOpenEvent.getMatcher(),
                SupervisorEvent.getMatcher(), VoteBoxEvent.getMatcher());
    }

    public byte[] getBlob() {
        int n = (int) (Math.random() * 100);
        byte[] array = new byte[n];
        for (int i = 0; i < n; i++)
            array[i] = (byte) (Math.random() * 256);
        return array;
    }

    public void testPollsOpen() {
        PollsOpenEvent event = new PollsOpenEvent(50, 123456, "hi");
        ASExpression sexp = event.toSExp();
        assertEquals("(polls-open 123456 hi)", sexp.toString());

        PollsOpenEvent event2 = (PollsOpenEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getTimestamp(), event2.getTimestamp());
        assertEquals(event.getKeyword(), event2.getKeyword());
    }

    public void testPollsClosed() {
        PollsClosedEvent event = new PollsClosedEvent(50, 123456);
        ASExpression sexp = event.toSExp();
        assertEquals("(polls-closed 123456)", sexp.toString());

        PollsClosedEvent event2 = (PollsClosedEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getTimestamp(), event2.getTimestamp());
    }

    public void testSupervisor() {
        SupervisorEvent event = new SupervisorEvent(50, 123456, "active");
        ASExpression sexp = event.toSExp();
        assertEquals("(supervisor 123456 active)", sexp.toString());

        SupervisorEvent event2 = (SupervisorEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getTimestamp(), event2.getTimestamp());
        assertEquals(event.getStatus(), event2.getStatus());
    }

    public void testVoteBox() {
        VoteBoxEvent event = new VoteBoxEvent(50, 3, "ready", 75, 20, 30);
        ASExpression sexp = event.toSExp();
        assertEquals("(votebox 3 ready 75 20 30)", sexp.toString());

        VoteBoxEvent event2 = (VoteBoxEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getStatus(), event2.getStatus());
        assertEquals(event.getLabel(), event2.getLabel());
        assertEquals(event.getBattery(), event2.getBattery());
        assertEquals(event.getPublicCount(), event2.getPublicCount());
        assertEquals(event.getProtectedCount(), event2.getProtectedCount());
    }

    public void testAssignLabel() {
        AssignLabelEvent event = new AssignLabelEvent(50, 65, 3);
        ASExpression sexp = event.toSExp();
        assertEquals("(assign-label 65 3)", sexp.toString());

        AssignLabelEvent event2 = (AssignLabelEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getNode(), event2.getNode());
        assertEquals(event.getLabel(), event2.getLabel());
    }

    public void testAuthorizedToCast() {
        byte[] nonce = getBlob();
        byte[] ballot = getBlob();
        AuthorizedToCastEvent event = new AuthorizedToCastEvent(50, 65, nonce,
                ballot);
        ASExpression sexp = event.toSExp();
        assertEquals("(authorized-to-cast 65 "
                + (new BigInteger(nonce)).toString() + " "
                + StringExpression.makeString(ballot).toString() + ")", sexp
                .toString());

        AuthorizedToCastEvent event2 = (AuthorizedToCastEvent) matcher.match(
                50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getNode(), event2.getNode());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
        assertTrue(Arrays.equals(event.getBallot(), event2.getBallot()));
    }

    public void testCastBallot() {
        ASExpression nonce = StringExpression.makeString(getBlob());
        ASExpression ballot = StringExpression.makeString(getBlob());
        CastBallotEvent event = new CastBallotEvent(50, nonce, ballot);
        ASExpression sexp = event.toSExp();
        assertEquals("(cast-ballot " + nonce.toString() + " "
                + ballot.toString() + ")", sexp.toString());

        CastBallotEvent event2 = (CastBallotEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getNonce(), event2.getNonce());
        assertEquals(event.getBallot(), event2.getBallot());
    }

    public void testBallotReceived() {
        byte[] nonce = getBlob();
        BallotReceivedEvent event = new BallotReceivedEvent(50, 65, nonce);
        ASExpression sexp = event.toSExp();
        assertEquals("(ballot-received 65 "
                + (new BigInteger(nonce)).toString() + ")", sexp.toString());

        BallotReceivedEvent event2 = (BallotReceivedEvent) matcher.match(50,
                sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getNode(), event2.getNode());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
    }

    public void testOverrideCancel() {
        byte[] nonce = getBlob();
        OverrideCancelEvent event = new OverrideCancelEvent(50, 65, nonce);
        ASExpression sexp = event.toSExp();
        assertEquals("(override-cancel 65 "
                + (new BigInteger(nonce)).toString() + ")", sexp.toString());

        OverrideCancelEvent event2 = (OverrideCancelEvent) matcher.match(50,
                sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getNode(), event2.getNode());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
    }

    public void testOverrideCast() {
        byte[] nonce = getBlob();
        OverrideCastEvent event = new OverrideCastEvent(50, 65, nonce);
        ASExpression sexp = event.toSExp();
        assertEquals("(override-cast 65 "
                + (new BigInteger(nonce)).toString() + ")", sexp.toString());

        OverrideCastEvent event2 = (OverrideCastEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getNode(), event2.getNode());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
    }

    public void testOverrideCancelConfirm() {
        byte[] nonce = getBlob();
        OverrideCancelConfirmEvent event = new OverrideCancelConfirmEvent(50,
                nonce);
        ASExpression sexp = event.toSExp();
        assertEquals("(override-cancel-confirm "
                + (new BigInteger(nonce)).toString() + ")", sexp.toString());

        OverrideCancelConfirmEvent event2 = (OverrideCancelConfirmEvent) matcher
                .match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
    }

    public void testOverrideCancelDeny() {
        byte[] nonce = getBlob();
        OverrideCancelDenyEvent event = new OverrideCancelDenyEvent(50, nonce);
        ASExpression sexp = event.toSExp();
        assertEquals("(override-cancel-deny "
                + (new BigInteger(nonce)).toString() + ")", sexp.toString());

        OverrideCancelDenyEvent event2 = (OverrideCancelDenyEvent) matcher
                .match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
    }

    public void testOverrideCastConfirm() {
        byte[] nonce = getBlob();
        byte[] ballot = getBlob();
        OverrideCastConfirmEvent event = new OverrideCastConfirmEvent(50,
                nonce, ballot);
        ASExpression sexp = event.toSExp();
        assertEquals("(override-cast-confirm "
                + (new BigInteger(nonce)).toString() + " "
                + StringExpression.makeString(ballot).toString() + ")", sexp
                .toString());

        OverrideCastConfirmEvent event2 = (OverrideCastConfirmEvent) matcher
                .match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
        assertTrue(Arrays.equals(event.getBallot(), event2.getBallot()));
    }

    public void testOverrideCastDeny() {
        byte[] nonce = getBlob();
        OverrideCastDenyEvent event = new OverrideCastDenyEvent(50, nonce);
        ASExpression sexp = event.toSExp();
        assertEquals("(override-cast-deny "
                + (new BigInteger(nonce)).toString() + ")", sexp.toString());

        OverrideCastDenyEvent event2 = (OverrideCastDenyEvent) matcher.match(
                50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertTrue(Arrays.equals(event.getNonce(), event2.getNonce()));
    }

    public void testLastPollsOpen() {
        LastPollsOpenEvent event = new LastPollsOpenEvent(50,
                new PollsOpenEvent(0, 123456, "hi"));
        ASExpression sexp = event.toSExp();
        assertEquals("(last-polls-open (polls-open 123456 hi))", sexp
                .toString());

        LastPollsOpenEvent event2 = (LastPollsOpenEvent) matcher
                .match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getPollsOpenMsg().getTimestamp(), event2
                .getPollsOpenMsg().getTimestamp());
        assertEquals(event.getPollsOpenMsg().getKeyword(), event2
                .getPollsOpenMsg().getKeyword());
    }

    public void testActivated() {
        ArrayList<StatusEvent> statuses = new ArrayList<StatusEvent>();
        SupervisorEvent supStatus = new SupervisorEvent(0, 123456, "active");
        VoteBoxEvent vbStatus = new VoteBoxEvent(0, 3, "ready", 75, 20, 30);
        statuses.add(new StatusEvent(0, 50, supStatus));
        statuses.add(new StatusEvent(0, 65, vbStatus));

        ActivatedEvent event = new ActivatedEvent(50, statuses);
        ASExpression sexp = event.toSExp();
        assertEquals(
                "(activated ((status 50 (supervisor 123456 active)) (status 65 (votebox 3 ready 75 20 30))))",
                sexp.toString());

        ActivatedEvent event2 = (ActivatedEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());

        SupervisorEvent supStatus2 = (SupervisorEvent) event2.getStatuses()
                .get(0).getStatus();
        assertEquals(supStatus.getTimestamp(), supStatus2.getTimestamp());
        assertEquals(supStatus.getStatus(), supStatus2.getStatus());

        VoteBoxEvent vbStatus2 = (VoteBoxEvent) event2.getStatuses().get(1).getStatus();
        assertEquals(vbStatus.getStatus(), vbStatus2.getStatus());
        assertEquals(vbStatus.getLabel(), vbStatus2.getLabel());
        assertEquals(vbStatus.getBattery(), vbStatus2.getBattery());
        assertEquals(vbStatus.getPublicCount(), vbStatus2.getPublicCount());
        assertEquals(vbStatus.getProtectedCount(), vbStatus2
                .getProtectedCount());

        event = new ActivatedEvent(50, new ArrayList<StatusEvent>());
        sexp = event.toSExp();
        assertEquals("(activated ())", sexp.toString());

        event2 = (ActivatedEvent) matcher.match(50, sexp);
        assertEquals(event.getSerial(), event2.getSerial());
        assertEquals(event.getStatuses(), event2.getStatuses());
    }
}
