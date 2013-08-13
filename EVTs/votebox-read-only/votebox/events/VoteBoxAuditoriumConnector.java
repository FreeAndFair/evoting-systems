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

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Observable;
import java.util.Observer;

import javax.swing.Timer;

import auditorium.IAuditoriumParams;
import auditorium.AuditoriumHost;
import auditorium.HostPointer;
import auditorium.NetworkException;
import auditorium.ReleasedQueueException;
import auditorium.AuditoriumHost.Pair;

/**
 * The VoteBoxAuditoriumConnecter is the "middleman" that starts an instance of
 * Auditorium, handles the VoteBox messaging protocol, and generates events to
 * the application.
 * 
 * @author cshaw
 */
public class VoteBoxAuditoriumConnector {

    private final AuditoriumHost auditorium;
    private final VoteBoxEventNotifier notifier;
    private final VoteBoxEventMatcher matcher;

    /**
     * Constructs a new VoteBoxAuditoriumConnector with the given serial number
     * and matcher rules to check against incoming announcements.
     * 
     * @param serial
     *            this machine's serial number
     * @param params
     *            parameters for configuring the connector
     * @param rules
     *            the matchers for messages this machine needs
     * @throws NetworkException
     */
    public VoteBoxAuditoriumConnector(int serial, 
			IAuditoriumParams params,
			MatcherRule... rules)
            throws NetworkException
	{
        notifier = new VoteBoxEventNotifier();
        auditorium = new AuditoriumHost( Integer.toString( serial ), params );
        matcher = new VoteBoxEventMatcher( rules );

        auditorium.registerForJoined( new Observer() {
            public void update(Observable o, Object arg) {
                HostPointer host = (HostPointer) arg;
                notifier.joined( new JoinEvent( Integer.parseInt( host
                        .getNodeId() ) ) );
            }
        } );
        auditorium.registerForLeft( new Observer() {
            public void update(Observable o, Object arg) {
                HostPointer host = (HostPointer) arg;
                notifier.left( new LeaveEvent( Integer.parseInt( host
                        .getNodeId() ) ) );
            }
        } );
        auditorium.start();
        initEventThread();
    }

    /**
     * Adds a listener for VoteBox events. The listeners are called in the order
     * that they are added.
     * 
     * @param l
     *            the listener
     */
    public void addListener(VoteBoxEventListener l) {
        notifier.addListener( l );
    }

    /**
     * Removes a listener from the list of VoteBox event listeners.
     * 
     * @param l
     *            the listener
     */
    public void removeListener(VoteBoxEventListener l) {
        notifier.removeListener( l );
    }

    /**
     * Attempts to connect to an auditorium by running discover once.
     * 
     * @throws NetworkException
     */
    public void connect() throws NetworkException {
        connect( 0, 0 );
    }

    /**
     * Attempts to connect to an auditorium, and if no hosts are discovered,
     * will wait a number of seconds and then try again
     * 
     * @param delay
     *            the wait time in between repeats
     * @param repeats
     *            the number of repeats (-1 to repeat forever)
     * @throws NetworkException
     */
    public void connect(final int delay, final int repeats)
            throws NetworkException {
        HostPointer[] hosts = auditorium.discover();
        // HostPointer[] hosts = { new HostPointer("1", "168.7.117.35", 9700),
        // new HostPointer("2", "168.7.117.36", 9700),
        // new HostPointer("3", "168.7.117.37", 9700),
        // new HostPointer("4", "168.7.117.38", 9700),
        // new HostPointer("5", "168.7.23.136", 9700) };
        for (HostPointer host : hosts) {
            if (!host.getNodeId().equals( auditorium.getNodeId() )) {
                try {
                    auditorium.join( host );
                    notifier.joined( new JoinEvent( Integer.parseInt( host
                            .getNodeId() ) ) );
                }
                catch (NetworkException e) {}
            }
        }

        // Repeat if necessary
        if (hosts.length == 0 && repeats > 0 && delay > 0) {
            Timer timer = new Timer( delay * 1000, new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    try {
                        connect( delay, repeats - 1 );
                    }
                    catch (NetworkException e1) {
                    	//NetworkException represents a recoverable error
                    	//  so just note it and continue
                        System.out.println("Recoverable error occured: "+e1.getMessage());
                        e1.printStackTrace(System.err);
                    }
                }
            } );
            timer.setRepeats( false );
            timer.start();
        }
    }

    /**
     * Disconnects from the auditorum network.
     */
    public void disconnect() {
        auditorium.disconnect();
    }

    /**
     * Broadcasts an announcement on the auditorium network. The event is then
     * fired, as if this node had heard the announcement from someone else. All
     * code that reacts to a message, whether sent by this machine or another,
     * should always exist in the listeners that are registered to the
     * VoteBoxAuditoriumConnector. This allows for an abstraction based on who
     * sent the message.
     * 
     * @param e
     *            the event to announce
     */
    public void announce(IAnnounceEvent e) {
        auditorium.announce( e.toSExp() );
        e.fire( notifier );
    }

    private void initEventThread() {
        new Thread() {
            @Override
            public void run() {
                boolean running = true;
                while (running) {
                    try {
                        Pair announce = auditorium.listen();
                        IAnnounceEvent event = matcher.match( Integer
                                .parseInt( announce.from.getNodeId() ),
                            announce.message );
                        
                        if (event != null){
                            event.fire( notifier );
                        }

                    }
                    catch (ReleasedQueueException e) {
                        running = false;
                        e.printStackTrace();
                    }
                }
            }
        }.start();
    }
}
