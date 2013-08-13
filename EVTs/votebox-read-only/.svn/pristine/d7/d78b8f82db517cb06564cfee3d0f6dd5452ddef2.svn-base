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

import org.junit.*;

import java.io.File;
import java.util.ArrayList;

import sexpression.*;

import auditorium.*;

/**
 * Tests for the Log class.
 * 
 * @author kyle
 * 
 */
public class LogTest {

    private Log _log;

    @Before
    public void setup() throws Exception {
        _log = new Log( new File( "temp" ) );
    }

    @After
    public void tear() {
        new File( "temp" ).delete();
    }

    // ** logAnnouncement(Message) tests

    @Test
    public void log_announcement_1() throws Exception {
        Message msg1 = new Message( "announcement", new HostPointer(
                "test-node", "192.168.1.100", 9000 ), "0",
                StringExpression.makeString( "test" ) );
        MessagePointer pointer1 = new MessagePointer( msg1 );
        Message msg2 = new Message( "announcement", new HostPointer(
                "test-node", "192.168.1.100", 9000 ), "1",
                StringExpression.makeString( "test2" ) );
        MessagePointer pointer2 = new MessagePointer( msg2 );

        assertFalse( _log.TESTgetSetCopy().contains( pointer1 ) );
        assertFalse( _log.TESTgetSetCopy().contains( pointer2 ) );
        assertEquals( 0, _log.getLast().length );

        _log.logAnnouncement( msg1 );

        ArrayList<MessagePointer> last = new ArrayList<MessagePointer>();
        for (MessagePointer p : _log.TESTgetLast())
            last.add( p );
        assertEquals( 1, _log.TESTgetSetCopy().size() );
        assertTrue( _log.TESTgetSetCopy().contains( pointer1 ) );
        assertFalse( _log.TESTgetSetCopy().contains( pointer2 ) );
        assertEquals( 1, last.size() );
        assertTrue( last.contains( pointer1 ) );
        assertFalse( last.contains( pointer2 ) );
        assertFalse( _log.logAnnouncement( msg1 ) );

        _log.logAnnouncement( msg2 );

        last = new ArrayList<MessagePointer>();
        for (MessagePointer p : _log.TESTgetLast())
            last.add( p );
        assertEquals( 2, _log.TESTgetSetCopy().size() );
        assertTrue( _log.TESTgetSetCopy().contains( pointer1 ) );
        assertTrue( _log.TESTgetSetCopy().contains( pointer2 ) );
        assertEquals( 2, last.size() );
        assertTrue( last.contains( pointer1 ) );
        assertTrue( last.contains( pointer2 ) );
        assertFalse( _log.logAnnouncement( msg1 ) );
        assertFalse( _log.logAnnouncement( msg2 ) );
    }
}
