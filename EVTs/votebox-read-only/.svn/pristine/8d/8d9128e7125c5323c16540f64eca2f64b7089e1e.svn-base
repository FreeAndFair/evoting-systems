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

package auditorium.test;

import static org.junit.Assert.*;

import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.StringExpression;
import auditorium.HostPointer;
import auditorium.IAuditoriumHost;
import auditorium.Link;
import auditorium.Log;
import auditorium.Message;
import auditorium.MessageSocket;
import auditorium.SynchronizedQueue;

public class LinkTest {

    // the host will put stuff in here when its methods are called.
    private SynchronizedQueue<Message> _received;
    private SynchronizedQueue<Link> _links;

    // Use this stream to send shit to the Link.
    private volatile OutputStream _stream;
    // This is the thing we're testing.
    private Link _link;

    private IAuditoriumHost _host = new IAuditoriumHost() {

        public ASExpression getAddresses() {
            throw new RuntimeException( "unused" );
        }

        public Log getLog() {
            throw new RuntimeException( "unused" );
        }

        public HostPointer getMe() {
            throw new RuntimeException( "unused" );
        }

        public String getNodeId() {
            throw new RuntimeException( "unused" );
        }

        public void receiveAnnouncement(Message message) {
            _received.push( message );
        }

        public void removeLink(Link link) {
            _links.push( link );
        }

        public String nextSequence() {
            throw new RuntimeException( "unused" );
        }
    };

    // Don't touch this.
    @Before
    public void setup() throws Exception {
        Thread.sleep( 100 );
        _received = new SynchronizedQueue<Message>();
        _links = new SynchronizedQueue<Link>();

        new Thread( new Runnable() {

            public void run() {
                try {
                    ServerSocket serversocket = new ServerSocket( 9000 );
                    Socket toLink = serversocket.accept();
                    _stream = toLink.getOutputStream();
                    serversocket.close();
                }
                catch (Exception e) {
                    e.printStackTrace();
                    fail();
                }
            }
        } ).start();

        Thread.sleep( 100 );
        HostPointer hp = new HostPointer( "", "127.0.0.1", 9000 );
        _link = new Link( _host, new MessageSocket( hp, 8000 ), hp );
        _link.start();
        Thread.sleep( 100 );
    }

    @After
    public void tear() throws Exception {
        Thread.sleep( 100 );
        _stream.close();
        _link.stop();
        Thread.sleep( 100 );
    }

    // Check that when you close the socket, the thing stops running
    @Test
    public void close_socket() throws Exception {
        _stream.close();
        Thread.sleep( 100 );
        assertFalse( _link.running() );

        assertEquals( 1, _links.size() );
        assertEquals( 0, _received.size() );

        assertSame( _link, _links.pop() );
    }

    // Send random bytes
    @Test
    public void random_bytes() throws Exception {
        assertTrue( _link.running() );
        _stream.write( 234 );
        Thread.sleep( 100 );

        assertFalse( _link.running() );

        assertEquals( 1, _links.size() );
        assertEquals( 0, _received.size() );

        assertSame( _link, _links.pop() );
    }

    // send s-expressions that aren't formatted well, make sure they don't
    // perkolate to the top.
    @Test
    public void non_message_1() throws Exception {
        assertTrue( _link.running() );
        _stream.write( ListExpression.EMPTY.toVerbatim() );
        Thread.sleep( 100 );

        assertTrue( _link.running() );

        assertEquals( 0, _links.size() );
        assertEquals( 0, _received.size() );
    }

    @Test
    public void non_message_2() throws Exception {
        assertTrue( _link.running() );
        _stream.write( new ListExpression( "Test", "Message" ).toVerbatim() );
        Thread.sleep( 100 );

        assertTrue( _link.running() );

        assertEquals( 0, _links.size() );
        assertEquals( 0, _received.size() );
    }

    @Test
    public void non_message_3() throws Exception {
        assertTrue( _link.running() );
        _stream.write( new ListExpression(
                StringExpression.makeString( "announcment" ), new ListExpression(
                        "nothost", "id", "ip", "9000" ), ListExpression.EMPTY )
                .toVerbatim() );
        Thread.sleep( 100 );

        assertTrue( _link.running() );

        assertEquals( 0, _links.size() );
        assertEquals( 0, _received.size() );
    }

    // Send good expressions, check that they get recevied.
    @Test
    public void message_1() throws Exception {
        Message m = new Message( "announcement", new HostPointer( "id", "ip",
                9000 ), "TEST", ListExpression.EMPTY );

        assertTrue( _link.running() );
        _stream.write( m.toASE().toVerbatim() );
        Thread.sleep( 100 );

        assertTrue( _link.running() );

        assertEquals( 0, _links.size() );
        assertEquals( 1, _received.size() );

        assertEquals( m.toASE(), _received.pop().toASE() );
    }
}
