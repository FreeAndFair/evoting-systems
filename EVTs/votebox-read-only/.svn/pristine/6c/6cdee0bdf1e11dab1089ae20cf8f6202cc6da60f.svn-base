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

import org.junit.Test;

import sexpression.ListExpression;
import sexpression.NoMatch;
import sexpression.Nothing;
import sexpression.StringExpression;
import sexpression.StringWildcard;

import auditorium.HostPointer;
import auditorium.IncorrectFormatException;
import auditorium.Message;
import auditorium.MessagePointer;

/**
 * These tests cover the MessagePointer class.
 * 
 * @author kyle
 * 
 */
public class MessagePointerTest {

    // ** <init>(String, String, ASExprsesion) **
    @Test
    public void test_1constructor_1() throws Exception {
        MessagePointer mp = new MessagePointer( "node", "number",
                StringExpression.EMPTY );
        assertEquals( "node", mp.getNodeId() );
        assertEquals( "number", mp.getNumber() );
        assertEquals( StringExpression.EMPTY, mp.getHash() );
        assertEquals( "{machine:node message:number}", mp.toString() );
        assertEquals( new ListExpression( "ptr", "node", "number", "" ), mp
                .toASE() );
    }

    @Test
    public void test_1constructor_2() throws Exception {
        MessagePointer mp = new MessagePointer( "node2", "number2",
                StringExpression.makeString( "bleh" ) );
        assertEquals( "node2", mp.getNodeId() );
        assertEquals( "number2", mp.getNumber() );
        assertEquals( StringExpression.makeString( "bleh" ), mp.getHash() );
        assertEquals( "{machine:node2 message:number2}", mp.toString() );
        assertEquals( new ListExpression( "ptr", "node2", "number2", "bleh" ),
            mp.toASE() );
    }

    // ** <init>(ASExpression) tests **
    // junk
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_3() throws Exception {
        new MessagePointer( NoMatch.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_4() throws Exception {
        new MessagePointer( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_5() throws Exception {
        new MessagePointer( StringWildcard.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_6() throws Exception {
        new MessagePointer( ListExpression.EMPTY );
    }

    // [0] isn't 'msg'
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_7() throws Exception {
        new MessagePointer( new ListExpression( "notmsg", "node", "1", "hash" ) );
    }

    // length >4
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_8() throws Exception {
        new MessagePointer( new ListExpression( "msg", "node", "1", "hash",
                "extra" ) );
    }

    // Good
    @Test
    public void test_2constructor_9() throws Exception {
        MessagePointer mp = new MessagePointer( new ListExpression( "ptr",
                "node", "1", "hash" ) );
        assertEquals( "node", mp.getNodeId() );
        assertEquals( "1", mp.getNumber() );
        assertEquals( StringExpression.makeString( "hash" ), mp.getHash() );
        assertEquals( "{machine:node message:1}", mp.toString() );
        assertEquals( new ListExpression( "ptr", "node", "1", "hash" ), mp
                .toASE() );
    }

    // ** <init>(Message) **
    HostPointer hp = new HostPointer( "1", "2", 3 );

    @Test
    public void test_3constructor_1() throws Exception {
        Message m = new Message( "type", hp, "asdf", ListExpression.EMPTY );
        MessagePointer mp = new MessagePointer( m );

        assertEquals( "1", mp.getNodeId() );
        assertEquals( "asdf", mp.getNumber() );
        assertEquals( m.getHash(), mp.getHash() );
    }
}
