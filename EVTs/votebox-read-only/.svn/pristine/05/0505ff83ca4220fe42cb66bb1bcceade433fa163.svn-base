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

package sexpression.lexer;

import java.io.IOException;
import java.io.Reader;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Queue;

/**
 * This class takes any input stream and scans for the following tokens:<br>
 * colon (':')<br>
 * open paren ('(')<br>
 * close paren (')')<br>
 * words dileneated by either whitespace or one of the above tokens.<br>
 * 
 * @author kyle
 * 
 */
public class Lexer implements ILexer {

    private final Reader _reader;
    private final Queue<Token> _queue;
    private final HashMap<Character, Token> _tokens;

    private ILexerState _state;

    /**
     * Construct a lexer which will read from the given character stream.
     * 
     * @param r
     *            The lexer will read from this character stream.
     */
    public Lexer(Reader r) {
        _reader = r;
        _queue = new LinkedList<Token>();
        _state = WhitespaceState.SINGLETON;
        _tokens = new HashMap<Character, Token>();

        _tokens.put( '(', Open.SINGLETON );
        _tokens.put( ')', Close.SINGLETON );
        _tokens.put( ':', Colon.SINGLETON );
        _tokens.put( '#', Hash.SINGLETON );
        _tokens.put( '%', Mod.SINGLETON );
    }

    /**
     * @see sexpression.lexer.ILexer#peek()
     */
    public Token peek() {
        fillQueue();
        return _queue.peek();
    }

    /**
     * @see sexpression.lexer.ILexer#read()
     */
    public Token read() {
        fillQueue();
        return _queue.remove();
    }

    /**
     * Add a token to the queue of tokens that have been scanned. This method
     * should be called by state instances.
     * 
     * @param t
     *            This is the token that was encountered and should be added to
     *            the queue.
     */
    public void add(Token t) {
        _queue.offer( t );
    }

    /**
     * Set the state of the lexer.
     * 
     * @param newstate
     *            This is the lexer state instance that will become the lexer's
     *            new state.
     */
    public void setState(ILexerState newstate) {
        _state = newstate;
    }

    private void fillQueue() {
        // If there is not at least one token in the queue, read characters from
        // the stream until the state instance places at least one there.
        while (_queue.peek() == null) {
            int c;
            try {
                c = _reader.read();
            }
            catch (IOException e) {
                _queue.add( EOF.SINGLETON );
                return;
            }

            if (c == -1)
                _state.readEOF( this );
            else if (c == '\n')
                _state.readEOL( this );
            else if (c == ';')
                _state.readComment( this );
            else if (Character.isWhitespace( c ))
                _state.readWhitespace( this );
            else if (_tokens.containsKey( (char) c ))
                _state.readSpecial( this, _tokens.get( (char) c ) );
            else
                _state.readCharacter( this, (char) c );
        }
    }
}
