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

import java.io.File;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import sexpression.*;
import auditorium.*;

public class TemporalLayerTest {

	private File _tmpFile;
    private Log _log;
    private IAuditoriumHost _host = new IAuditoriumHost() {

        public ASExpression getAddresses() {
            throw new RuntimeException( "not used" );
        }

        public Log getLog() {
            return _log;
        }

        public HostPointer getMe() {
            throw new RuntimeException( "not used" );
        }

        public String getNodeId() {
            throw new RuntimeException( "not used" );
        }

        public void receiveAnnouncement(Message message) {
            throw new RuntimeException( "not used" );
        }

        public void removeLink(Link link) {
            throw new RuntimeException( "not used" );
        }

        public String nextSequence() {
            throw new RuntimeException( "not used" );
        }
    };
    private AuditoriumTemporalLayer _layer;

    @Before
    public void setup() throws Exception {
    	_tmpFile = File.createTempFile("tmp", "test");
    	
        _log = new Log( _tmpFile );
        _layer = new AuditoriumTemporalLayer( AAuditoriumLayer.BOTTOM, _host );
    }

    @After
    public void tear() {
        _tmpFile.delete();
    }

    // ** makeAnnouncement(ASExpression) tests **
    // Empty log.
    /**
     * Creates an announcement, makes sure that the thing that was wrapped ends
     * up in the datum section, then returns the pointer list for checking by
     * the caller.
     */
    private ASExpression test_makeAnnouncement(ASExpression wrapthis)
            throws Exception {
        ListExpression datum = (ListExpression) _layer
                .makeAnnouncement( wrapthis );
        ListExpression result = (ListExpression) AuditoriumTemporalLayer.PATTERN
                .match( datum );

        assertNotSame( result, NoMatch.SINGLETON );
        assertEquals( wrapthis, result.get( 1 ) );
        return result.get( 0 );
    }

    @Test
    public void test_makeannounement_4() throws Exception {
        assertEquals( ListExpression.EMPTY,
            test_makeAnnouncement( ListExpression.EMPTY ) );
    }

    @Test
    public void test_makeannounement_5() throws Exception {
        assertEquals( ListExpression.EMPTY,
            test_makeAnnouncement( StringExpression.EMPTY ) );
    }

    @Test
    public void test_makeannounement_6() throws Exception {
        assertEquals( ListExpression.EMPTY,
            test_makeAnnouncement( StringExpression.makeString( "TEST" ) ) );
    }

    @Test
    public void test_makeannouncement_7() throws Exception {
        assertEquals( ListExpression.EMPTY,
            test_makeAnnouncement( new ListExpression( StringExpression.makeString(
                    "TEST" ), StringExpression.makeString( "TEST2" ) ) ) );
    }

    // Two things in the log.
    HostPointer hp = new HostPointer( "host", "ip", 200 );
    Message m1 = new Message( "announcement", hp, "1", StringExpression.makeString(
            "msg" ) );
    Message m2 = new Message( "announcement2", hp, "2", StringExpression.makeString(
            "msg" ) );

    @Test
    public void test_makeannouncement_8() throws Exception {
        _log.logAnnouncement( m1 );
        _log.logAnnouncement( m2 );

        assertEquals( new ListExpression( new MessagePointer( m1 ).toASE(),
                new MessagePointer( m2 ).toASE() ),
            test_makeAnnouncement( ListExpression.EMPTY ) );
    }

    // ** makeJoinReply(ASExpression) tests **
    @Test
    public void test_makejoin_1() throws Exception {
        assertEquals( ListExpression.EMPTY, _layer
                .makeJoinReply( ListExpression.EMPTY ) );
    }

    @Test
    public void test_makejoin_2() throws Exception {
        assertEquals( ListExpression.EMPTY, _layer
                .makeJoinReply( Nothing.SINGLETON ) );
    }

    @Test
    public void test_makejoin_3() throws Exception {
        _log.logAnnouncement( m1 );

        assertEquals( new ListExpression( new MessagePointer( m1 ).toASE() ),
            _layer.makeJoinReply( StringExpression.makeString( "asf" ) ) );
    }

    @Test
    public void test_makejoin_4() throws Exception {
        _log.logAnnouncement( m1 );
        _log.logAnnouncement( m2 );

        assertEquals( new ListExpression( new MessagePointer( m1 ).toASE(),
                new MessagePointer( m2 ).toASE() ), _layer
                .makeJoinReply( StringExpression.EMPTY ) );
    }

    // ** receiveAnnouncement(ASExpression) tests **
    // Junk
    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_1() throws Exception {
        _layer.receiveAnnouncement( NoMatch.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_2() throws Exception {
        _layer.receiveAnnouncement( Wildcard.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_3() throws Exception {
        _layer.receiveAnnouncement( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_4() throws Exception {
        _layer.receiveAnnouncement( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_5() throws Exception {
        _layer
                .receiveAnnouncement( new ListExpression( "Check", "one", "two" ) );
    }

    // [0] != succeeds
    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_6() throws Exception {
        _layer
                .receiveAnnouncement( new ListExpression( StringExpression.makeString(
                        "not-succeeds" ), ListExpression.EMPTY,
                        StringExpression.EMPTY ) );
    }

    // pointer list spot isn't a list at all
    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_7() throws Exception {
        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), StringExpression.EMPTY, StringExpression.EMPTY ) );
    }

    // pointer list has one element that doesn't match the pattern
    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_8() throws Exception {
        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), new ListExpression( new ListExpression( "ptr",
                "node", "1", "" ), new ListExpression( "ptr", "node", "1", "",
                "extra" ), new ListExpression( "ptr", "node", "1", "" ) ),
                StringExpression.EMPTY ) );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_9() throws Exception {
        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), new ListExpression( new ListExpression( "ptr",
                "node", "1", "" ), new ListExpression( StringExpression.makeString(
                "ptr" ), StringExpression.makeString( "node" ), StringExpression.makeString(
                "1" ), ListExpression.EMPTY ), new ListExpression( "ptr",
                "node", "1", "" ) ), StringExpression.EMPTY ) );
    }

    // pointer list has one element that matches the pattern, but can't be
    // parsed into a pointer
    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_10() throws Exception {
        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), new ListExpression( new ListExpression( "ptr",
                "node", "1", "" ), new ListExpression( "notptr", "node", "1",
                "" ), new ListExpression( "ptr", "node", "1", "" ) ),
                StringExpression.EMPTY ) );
    }

    // length > 3
    @Test(expected = IncorrectFormatException.class)
    public void test_receiveannouncement_11() throws Exception {
        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), new ListExpression( new ListExpression( "ptr",
                "node", "1", "" ),
                new ListExpression( "ptr", "node", "1", "" ),
                new ListExpression( "ptr", "node", "1", "" ) ),
                StringExpression.EMPTY, StringExpression.makeString( "extra" ) ) );
    }

    // Good
    @Test
    public void test_receiveannouncement_12() throws Exception {
        _log.logAnnouncement( m1 );
        assertEquals( 1, _log.TESTgetLast().size() );
        assertEquals( new MessagePointer( m1 ), _log.TESTgetLast().get( 0 ) );

        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), new ListExpression( new MessagePointer( m1 )
                .toASE() ), StringExpression.makeString( "TEST DATUM" ) ) );

        assertEquals( 0, _log.TESTgetLast().size() );
    }

    @Test
    public void test_receiveannouncement_13() throws Exception {
        _log.logAnnouncement( m1 );
        _log.logAnnouncement( m2 );
        assertEquals( 2, _log.TESTgetLast().size() );
        assertEquals( new MessagePointer( m1 ), _log.TESTgetLast().get( 0 ) );
        assertEquals( new MessagePointer( m2 ), _log.TESTgetLast().get( 1 ) );

        _layer.receiveAnnouncement( new ListExpression( StringExpression.makeString(
                "succeeds" ), new ListExpression( new MessagePointer( m1 )
                .toASE() ), StringExpression.makeString( "TEST DATUM" ) ) );

        assertEquals( 1, _log.TESTgetLast().size() );
        assertEquals( new MessagePointer( m2 ), _log.TESTgetLast().get( 0 ) );
    }

    // ** receiveJoinReply(ASExpression) tests **
    // Junk
    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_1() throws Exception {
        _layer.receiveJoinReply( NoMatch.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_2() throws Exception {
        _layer.receiveJoinReply( Wildcard.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_3() throws Exception {
        _layer.receiveJoinReply( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_4() throws Exception {
        _layer.receiveJoinReply( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_5() throws Exception {
        _layer.receiveJoinReply( new ListExpression( "Check", "one", "two" ) );
    }

    // not a list
    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_6() throws Exception {
        _layer.receiveJoinReply( StringExpression.makeString( "This is not a list" ) );
    }

    // a list, but not all the members match the pattern
    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_7() throws Exception {
        _layer.receiveJoinReply( new ListExpression( new MessagePointer( m1 )
                .toASE(), new ListExpression( "ptr", "hostid", "number",
                "hash", "EXTRA" ), new MessagePointer( m2 ).toASE() ) );
    }

    // all the members match the pattern, but pointers can't be construted out
    // of them.
    @Test(expected = IncorrectFormatException.class)
    public void test_receivejoinreply_8() throws Exception {
        _layer.receiveJoinReply( new ListExpression( new MessagePointer( m1 )
                .toASE(), new ListExpression( "notptr", "hostid", "number",
                "hash" ), new MessagePointer( m2 ).toASE() ) );
    }

    // Good.
    @Test
    public void test_receivejoinreply_9() throws Exception {
        assertEquals( 0, _log.TESTgetLast().size() );

        _layer.receiveJoinReply( new ListExpression( new MessagePointer( m1 )
                .toASE() ) );

        assertEquals( 1, _log.TESTgetLast().size() );
        assertEquals( new MessagePointer( m1 ), _log.TESTgetLast().get( 0 ) );
    }

    @Test
    public void test_receivejoinreply_10() throws Exception {
        assertEquals( 0, _log.TESTgetLast().size() );

        _layer.receiveJoinReply( new ListExpression( new MessagePointer( m1 )
                .toASE() ) );
        _layer.receiveJoinReply( new ListExpression( new MessagePointer( m2 )
                .toASE() ) );

        assertEquals( 2, _log.TESTgetLast().size() );
        assertEquals( new MessagePointer( m1 ), _log.TESTgetLast().get( 0 ) );
        assertEquals( new MessagePointer( m2 ), _log.TESTgetLast().get( 1 ) );
    }
}
