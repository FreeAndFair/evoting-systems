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

package sexpression.lexer.test;

import static org.junit.Assert.*;

import java.io.*;

import org.junit.Test;

import sexpression.lexer.*;

/**
 * This classes contains JUnit tests for the Lexer class.
 * 
 * @author kyle
 * 
 */
public class LexerTest {

    private Lexer _lex;

    /**
     * Set up the lexer to read from the stream of characters given.
     * 
     * @param inbuffer
     *            Interpret this string as a stream of characters and read from
     *            it.
     */
    private void setup(String inbuffer) throws Exception {
        _lex = new Lexer( new CharArrayReader( inbuffer.toCharArray() ) );
    }

    @Test
    public void empty() throws Exception {
        setup( "" );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
    }

    @Test
    public void whitespace() throws Exception {
        setup( "      \n\n  \n" );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
    }

    @Test
    public void close() throws Exception {
        setup( ")" );
        assertEquals( Close.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
    }

    @Test
    public void colon() throws Exception {
        setup( ":" );
        assertEquals( Colon.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
    }

    @Test
    public void words() throws Exception {
        setup( "one two" );
        assertEquals( new Word( "one" ), _lex.read() );
        assertEquals( new Word( "two" ), _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
    }

    @Test
    public void mixed() throws Exception {
        setup( "        one (((  ( : )::)two!? :" );
        assertEquals( new Word( "one" ), _lex.read() );
        assertEquals( Open.SINGLETON, _lex.read() );
        assertEquals( Open.SINGLETON, _lex.peek() );
        assertEquals( Open.SINGLETON, _lex.read() );
        assertEquals( Open.SINGLETON, _lex.read() );
        assertEquals( Open.SINGLETON, _lex.peek() );
        assertEquals( Open.SINGLETON, _lex.read() );
        assertEquals( Colon.SINGLETON, _lex.read() );
        assertEquals( Close.SINGLETON, _lex.read() );
        assertEquals( Colon.SINGLETON, _lex.read() );
        assertEquals( Colon.SINGLETON, _lex.peek() );
        assertEquals( Colon.SINGLETON, _lex.read() );
        assertEquals( Close.SINGLETON, _lex.read() );
        assertEquals( new Word( "two!?" ), _lex.read() );
        assertEquals( Colon.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.read() );
        assertEquals( EOF.SINGLETON, _lex.peek() );
        assertEquals( EOF.SINGLETON, _lex.read() );
    }
}
