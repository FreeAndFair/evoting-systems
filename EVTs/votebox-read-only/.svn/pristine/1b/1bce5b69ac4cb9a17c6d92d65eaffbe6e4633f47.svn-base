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

import sexpression.NoMatch;
import sexpression.Nothing;
import sexpression.StringExpression;
import sexpression.ListExpression;

import auditorium.HostPointer;
import auditorium.IncorrectFormatException;

/**
 * This is a JUnit test of the auditorium.HostPointer class.
 * 
 * @author kyle
 * 
 */
public class HostPointerTest {

    // ** <init>(String, String, int) tests **
    @Test
    public void test_1constructor_1() throws Exception {
        HostPointer hp = new HostPointer( "id", "ip", 1 );
        assertEquals( hp.getIP(), "ip" );
        assertEquals( hp.getNodeId(), "id" );
        assertEquals( hp.getPort(), 1 );
        assertEquals( hp.toASE(), new ListExpression( "host", "id", "ip", "1" ) );
        assertEquals( hp.toString(), "id@ip:1" );
    }

    @Test
    public void test_1constructor_2() throws Exception {
        HostPointer hp = new HostPointer( "node_id", "node_ip", 15000 );
        assertEquals( hp.getIP(), "node_ip" );
        assertEquals( hp.getNodeId(), "node_id" );
        assertEquals( hp.getPort(), 15000 );
        assertEquals( hp.toASE(), new ListExpression( "host", "node_id",
                "node_ip", "15000" ) );
        assertEquals( hp.toString(), "node_id@node_ip:15000" );
    }

    // **<init>(ASExpression) tests **
    // junk
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_1() throws Exception {
        new HostPointer( Nothing.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_2() throws Exception {
        new HostPointer( NoMatch.SINGLETON );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_3() throws Exception {
        new HostPointer( ListExpression.EMPTY );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_4() throws Exception {
        new HostPointer( StringExpression.EMPTY );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_5() throws Exception {
        new HostPointer( StringExpression.makeString( "TEST" ) );
    }

    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_6() throws Exception {
        new HostPointer( new ListExpression( StringExpression.makeString( "TEST" ),
                StringExpression.makeString( "TEST" ) ) );
    }

    // [0] != "host"
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_7() throws Exception {
        new HostPointer( new ListExpression( StringExpression.makeString( "" ),
                StringExpression.makeString( "host" ), StringExpression.makeString( "ip" ),
                StringExpression.makeString( "2000" ) ) );
    }

    // [0] !instanceof String
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_8() throws Exception {
        new HostPointer( new ListExpression( ListExpression.EMPTY,
                StringExpression.makeString( "host" ), StringExpression.makeString( "ip" ),
                StringExpression.makeString( "2000" ) ) );
    }

    // length > 4
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_9() throws Exception {
        new HostPointer(
                new ListExpression( StringExpression.makeString( "host" ),
                        StringExpression.makeString( "host" ), StringExpression.makeString(
                                "ip" ), StringExpression.makeString( "2000" ),
                        StringExpression.makeString( "extra" ) ) );
    }

    // [3] ! an int
    @Test(expected = IncorrectFormatException.class)
    public void test_2constructor_10() throws Exception {
        new HostPointer( new ListExpression( StringExpression.makeString( "host" ),
                StringExpression.makeString( "host" ), StringExpression.makeString( "ip" ),
                StringExpression.makeString( "2000a" ) ) );
    }

    // Good checking
    @Test
    public void test_2constructor_11() throws Exception {
        HostPointer hp = new HostPointer( new ListExpression(
                StringExpression.makeString( "host" ), StringExpression.makeString( "id" ),
                StringExpression.makeString( "ip" ), StringExpression.makeString( "2000" ) ) );

        assertEquals( hp.getIP(), "ip" );
        assertEquals( hp.getNodeId(), "id" );
        assertEquals( hp.getPort(), 2000 );
        assertEquals( hp.toASE(), new ListExpression( StringExpression.makeString(
                "host" ), StringExpression.makeString( "id" ), StringExpression.makeString(
                "ip" ), StringExpression.makeString( "2000" ) ) );
        assertEquals( hp.toString(), "id@ip:2000" );
    }

    @Test
    public void test_2constructor_12() throws Exception {
        HostPointer hp = new HostPointer( new ListExpression(
                StringExpression.makeString( "host" ),
                StringExpression.makeString( "host-id" ), StringExpression.makeString(
                        "host-ip" ), StringExpression.makeString( "2053" ) ) );

        assertEquals( hp.getIP(), "host-ip" );
        assertEquals( hp.getNodeId(), "host-id" );
        assertEquals( hp.getPort(), 2053 );
        assertEquals( hp.toASE(), new ListExpression( StringExpression.makeString(
                "host" ), StringExpression.makeString( "host-id" ),
                StringExpression.makeString( "host-ip" ),
                StringExpression.makeString( "2053" ) ) );
        assertEquals( hp.toString(), "host-id@host-ip:2053" );
    }

    // ** override equals(Object) tests **
    @Test
    public void test_equals_1() throws Exception {
        HostPointer one1 = new HostPointer( "id-1", "ip-1", 9000 );
        HostPointer one2 = new HostPointer( "id-1", "ip-1", 9000 );
        HostPointer two1 = new HostPointer( "id-2", "ip-2", 9000 );
        HostPointer two2 = new HostPointer( "id-2", "ip-2", 9000 );

        assertEquals( one1, one1 );
        assertEquals( one1, one2 );
        assertEquals( one1.hashCode(), one1.hashCode() );
        assertEquals( one2.hashCode(), one2.hashCode() );

        assertEquals( two1, two1 );
        assertEquals( two1, two2 );
        assertEquals( two1.hashCode(), two1.hashCode() );
        assertEquals( two2.hashCode(), two2.hashCode() );

        assertFalse( one1.equals( two1 ) );
        assertFalse( one1.equals( two2 ) );

        assertFalse( one2.equals( two1 ) );
        assertFalse( one2.equals( two2 ) );
    }
}
