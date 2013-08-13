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

package sexpression.test;

import static org.junit.Assert.*;

import org.junit.Test;

import sexpression.ByteArrayBuffer;
import sexpression.ByteArrayBuffer.ByteArray;

/**
 * This is a JUnit test of sexpression.ByteArrayBuffer.
 * 
 * @author kyle
 * 
 */
public class ByteArrayBufferTest {

    private ByteArrayBuffer _buffer;

    // ** <init>() tests **
    @Test
    public void test_1constructor() {
        _buffer = new ByteArrayBuffer();
        byte[] array = _buffer.getBytes();

        assertEquals( 0, array.length );
    }

    // ** <init>(ByteArray) tests **
    /**
     * @param bytes
     *            Use the constructor of ByteArrayBuffer to initialiize the byte
     *            array with these bytes.
     */
    private void setup_1(Byte... bytes) {
        byte[] b = new byte[bytes.length];
        for (int lcv = 0; lcv < bytes.length; lcv++)
            b[lcv] = bytes[lcv];
        _buffer = new ByteArrayBuffer();
        _buffer.append( new ByteArray( b ) );
    }

    @Test
    public void test_2constructor_1() {
        setup_1();
        assertEquals( 0, _buffer.getBytes().length );
    }

    @Test
    public void test_2constructor_2() {
        setup_1( (byte) 0 );
        byte[] bytes = _buffer.getBytes();
        assertEquals( 1, bytes.length );
        assertEquals( (byte) 0, bytes[0] );
    }

    @Test
    public void test_2constructor_3() {
        setup_1( (byte) 0, (byte) 0, (byte) 3, (byte) 4 );
        byte[] bytes = _buffer.getBytes();
        assertEquals( 4, bytes.length );
        assertEquals( (byte) 0, bytes[0] );
        assertEquals( (byte) 0, bytes[1] );
        assertEquals( (byte) 3, bytes[2] );
        assertEquals( (byte) 4, bytes[3] );
    }

    // ** append(ByteArray) tests **
    /**
     * @param bytes
     *            Use the append function to add these bytes to the currently
     *            constructed _buffer.
     */
    private void setup_2(Byte... bytes) {
        byte[] b = new byte[bytes.length];
        for (int lcv = 0; lcv < bytes.length; lcv++)
            b[lcv] = bytes[lcv];

        _buffer.append( new ByteArray( b ) );
    }

    @Test
    public void test_1append_1() {
        setup_1();
        setup_2();
        assertEquals( 0, _buffer.getBytes().length );
    }

    @Test
    public void test_1append_2() {
        setup_1();
        setup_2( (byte) 0 );
        setup_2( (byte) 1, (byte) 2 );

        byte[] b = _buffer.getBytes();
        assertEquals( 3, b.length );
        assertEquals( (byte) 0, b[0] );
        assertEquals( (byte) 1, b[1] );
        assertEquals( (byte) 2, b[2] );
    }

    @Test
    public void test_1append_3() {
        setup_1();
        setup_2( (byte) 0, (byte) 5 );
        setup_2( (byte) 133, (byte) 12, (byte) 25 );
        setup_2( (byte) 2, (byte) 23, (byte) 2, (byte) 234, (byte) 255,
            (byte) 0 );

        byte[] b = _buffer.getBytes();
        assertEquals( 11, b.length );
        assertEquals( (byte) 0, b[0] );
        assertEquals( (byte) 5, b[1] );
        assertEquals( (byte) 133, b[2] );
        assertEquals( (byte) 12, b[3] );
        assertEquals( (byte) 25, b[4] );
        assertEquals( (byte) 2, b[5] );
        assertEquals( (byte) 23, b[6] );
        assertEquals( (byte) 2, b[7] );
        assertEquals( (byte) 234, b[8] );
        assertEquals( (byte) 255, b[9] );
        assertEquals( (byte) 0, b[10] );
    }

    // ** append(ByteArrayBuffer) tests **
    @Test
    public void test_2append_1() {
        setup_1();

        ByteArrayBuffer buf = new ByteArrayBuffer();
        byte[] bytes = {
                23, 21, 1, 4, 12, 23, 123, 5, 13
        };
        buf.append( new ByteArray( bytes ) );

        _buffer.append( buf );
        _buffer.append( buf );

        byte[] b = _buffer.getBytes();

        assertEquals( 18, _buffer.getBytes().length );
        assertEquals( (byte) 23, b[0] );
        assertEquals( (byte) 21, b[1] );
        assertEquals( (byte) 1, b[2] );
        assertEquals( (byte) 4, b[3] );
        assertEquals( (byte) 12, b[4] );
        assertEquals( (byte) 23, b[5] );
        assertEquals( (byte) 123, b[6] );
        assertEquals( (byte) 5, b[7] );
        assertEquals( (byte) 13, b[8] );
        assertEquals( (byte) 23, b[9] );
        assertEquals( (byte) 21, b[10] );
        assertEquals( (byte) 1, b[11] );
        assertEquals( (byte) 4, b[12] );
        assertEquals( (byte) 12, b[13] );
        assertEquals( (byte) 23, b[14] );
        assertEquals( (byte) 123, b[15] );
        assertEquals( (byte) 5, b[16] );
        assertEquals( (byte) 13, b[17] );

    }
}
