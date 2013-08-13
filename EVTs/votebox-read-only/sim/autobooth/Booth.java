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

package sim.autobooth;

import sim.utils.*;

import sexpression.*;
import auditorium.*;
import votebox.*;
import votebox.events.*;

import java.util.*;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.Timer;

public class Booth {
    public static final String OPT_ID = "id";
    public static final String OPT_VOTE_MIN_TIME = "vote-min-time";
    public static final String OPT_VOTE_MAX_TIME = "vote-max-time";
    public static final String OPT_AUDITORIUM_PARAMS_FILE = "conf";

    private VoteBoxAuditoriumConnector 	_auditorium;
    private Timer 						_statusTimer;

    private AuditoriumParams 			_auditoriumParams;
    private int 						_nodeid = -1;
    private int 						_label = -1;
    private int 						_battery = 42;

    private boolean 					_voting = false;
    private int 						_protectedCount = 0;
    private int 						_publicCount = 0;

    private byte[] 						_ballotNonce;

    private int 						_voteMinTime;
    private int 						_voteMaxTime;

    public Booth(HashMap<String, Object> opts) {
        _nodeid = new Integer(opts.get(OPT_ID).toString());
        _voteMinTime = new Integer(opts.get(OPT_VOTE_MIN_TIME).toString());
        _voteMaxTime = new Integer(opts.get(OPT_VOTE_MAX_TIME).toString());
        _auditoriumParams = new AuditoriumParams(
        		opts.get(OPT_AUDITORIUM_PARAMS_FILE).toString());
    }

    public void reset() {
        _voting = false;
        _ballotNonce = null;

        _statusTimer = new Timer(30 * Time.MINUTES, new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                _auditorium.announce(makeStatusEvent());
            }
        });
    }

    public VoteBoxEvent makeStatusEvent() {
        return new VoteBoxEvent(_nodeid, _label,
                (_voting ? "in-use" : "ready"), 
                _battery, _protectedCount, _publicCount);
    }

    public void broadcastStatus() {
        _auditorium.announce(makeStatusEvent());
        _statusTimer.restart();
    }

    public void doCastBallot() {
        System.out.println("Casting ballot.");

        _auditorium.announce(new CastBallotEvent(_nodeid, StringExpression
                .makeString(_ballotNonce), StringExpression
                .makeString("cast ballot goes here")));
        _protectedCount++;
        _publicCount++;
        _voting = false;
    }

    public void start() {
        reset();

        try {
            _auditorium = new VoteBoxAuditoriumConnector(_nodeid,
                    _auditoriumParams, ActivatedEvent.getMatcher(),
                    AssignLabelEvent.getMatcher(), AuthorizedToCastEvent.getMatcher(),
                    BallotReceivedEvent.getMatcher(), OverrideCancelEvent.getMatcher(),
                    OverrideCastEvent.getMatcher(), PollsOpenQEvent.getMatcher());
        } catch (NetworkException e1) {
            System.err.println("Error while initializing Auditorium:");
            e1.printStackTrace();
            System.exit(-1);
        }

        _auditorium.addListener(new VoteBoxEventListener() {
            // Much of this is cloned from votebox/VoteBox.java
            // [dsandler 09/23/2007]

        	public void ballotCounted(BallotCountedEvent e){
        		//NO-OP
        	}
        	
            /**
             * Handler for the activated message. Look to see if this VoteBox's
             * status exists (and is correct), and if not, broadcast its status
             */
            public void activated(ActivatedEvent e) {
                System.out.println("*** activated: " + e.toString());

                boolean found = false;
                for (StatusEvent ae : e.getStatuses()) {
                    if (ae.getNode() == _nodeid) {
                        VoteBoxEvent ve = (VoteBoxEvent) ae.getStatus();
                        VoteBoxEvent status = makeStatusEvent();
                        if (!ve.getStatus().equals(status.getStatus())
                                || ve.getBattery() != status.getBattery()
                                || ve.getLabel() != status.getLabel()
                                || ve.getProtectedCount() != status
                                        .getProtectedCount()
                                || ve.getPublicCount() != status
                                        .getPublicCount())
                            broadcastStatus();
                        found = true;
                    }
                }
                if (!found)
                    broadcastStatus();
            }

            /**
             * Handler for the assign-label message. If it is referring to this
             * booth, set the label.
             */
            public void assignLabel(AssignLabelEvent e) {
                System.out.println("*** assign-label: " + e.toString());

                if (e.getNode() == _nodeid)
                    _label = e.getLabel();
            }

            /**
             * Handler for the authorized-to-cast message. If it is for this
             * booth, and it is not already voting, unzip the ballot and fire
             * the VoteBox runtime. Also announce the new status.
             */
            public void authorizedToCast(AuthorizedToCastEvent e) {
                System.out.println("*** authorized-to-cast: " + e.toString());

                if (e.getNode() == _nodeid) {
                    System.out.println("*** it's for me!");
                    _ballotNonce = e.getNonce();
                    _voting = true;
                    broadcastStatus();
                    int voteTime = _voteMinTime
                    		+ (int)(Math.random() * (_voteMaxTime - _voteMinTime));
                    System.out.println("*** will send cast ballot in "
                    		+ voteTime + " ms.");
                    Timer t = new Timer(voteTime,
                    		new ActionListener() {
                    	public void actionPerformed(ActionEvent foo) {
                    		doCastBallot();
                    	}
                    });
                    t.setRepeats(false);
                    t.start();
                }
            }

            public void pollsClosed(PollsClosedEvent e) {
                System.out.println("*** polls-closed. Shutting down in 15 seconds...");

                Timer t = new Timer(15 * Time.SECONDS,
                		new ActionListener() {
                    public void actionPerformed(ActionEvent foo) {
                        _auditorium.disconnect();
                        try {
                            Thread.sleep(15 * Time.SECONDS);
                        } catch (InterruptedException e) { }
                        System.out.println("Exiting.");
                        System.exit(0);
                    }
                });
                t.setRepeats(false);
                t.start();
            }

            public void pollsOpen(PollsOpenEvent e) {
                System.out.println("*** polls-open: " + e.toString());
            }

            public void overrideCastConfirm(OverrideCastConfirmEvent e) { }
            public void overrideCastDeny(OverrideCastDenyEvent e) { }
            public void ballotReceived(BallotReceivedEvent e) { }
            public void castBallot(CastBallotEvent e) { }
            public void joined(JoinEvent e) { }
            public void lastPollsOpen(LastPollsOpenEvent e) { }
            public void left(LeaveEvent e) { }
            public void overrideCancelConfirm(OverrideCancelConfirmEvent e) { }
            public void overrideCancelDeny(OverrideCancelDenyEvent e) { }
            public void pollsOpenQ(PollsOpenQEvent e) { }
            public void supervisor(SupervisorEvent e) { }
            public void votebox(VoteBoxEvent e) { }
            
            public void overrideCancel(OverrideCancelEvent e) {
                System.out.println("*** override-cancel: " + e.toString());

                if (_voting 
                		&& _nodeid == e.getNode()
                		&& Arrays.equals(e.getNonce(), _ballotNonce)) {
                	// pass
                }
            }

            public void overrideCast(OverrideCastEvent e) {
                System.out.println("*** override-cast: " + e.toString());

                if (_voting && _nodeid == e.getNode()
                        && Arrays.equals(e.getNonce(), _ballotNonce)) {
                    // pass
                }
            }

            public void challengeResponse(ChallengeResponseEvent e) {
                // NO-OP

            }
            
            public void challenge(ChallengeEvent e) {
                // NO-OP

            }

            public void commitBallot(CommitBallotEvent e) {
                // NO-OP

            }

        });

        try {
            System.out.println(">>> connecting to Auditorium...");

            _auditorium.connect();
            _auditorium.announce(makeStatusEvent());
        } catch (NetworkException e1) {
        	//NetworkException represents a recoverable error
        	//  so just note it and continue
            System.out.println("Recoverable error occured: "+e1.getMessage());
            e1.printStackTrace(System.err);
        }

        _statusTimer.start();
    }

    public static void main(String[] args) {
        HashMap<String, Object> opts = new HashMap<String, Object>();
        opts.put(OPT_AUDITORIUM_PARAMS_FILE, "vb.conf");
        opts.put(OPT_VOTE_MIN_TIME, 3 * Time.MINUTES);
        opts.put(OPT_VOTE_MAX_TIME, 15 * Time.MINUTES);

        ArgParse.addArgsToMap(args, opts);

        if (!opts.containsKey("id")) {
            System.err.println("error: node id not set; use id=X on command line");
            System.exit(-1);
        }

        new Booth(opts).start();
    }
}
