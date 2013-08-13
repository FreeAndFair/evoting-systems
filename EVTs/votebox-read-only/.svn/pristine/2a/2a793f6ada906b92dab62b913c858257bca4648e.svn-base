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

/**
 * <b>State Design Pattern</b><br>
 * <br>
 * When the lexer is in this state, is in the middle of reading a word. This
 * state instance is not a singleton, because it must keep track of charcaters
 * read in the word that it is in the middle of reading.
 * 
 * @author kyle
 * 
 */
public class WordState implements ILexerState {

    private StringBuffer _buffer;

    public WordState() {
        _buffer = new StringBuffer();
    }

    /**
     * @see sexpression.lexer.ILexerState#readCharacter(sexpression.lexer.Lexer,
     *      char)
     */
    public void readCharacter(Lexer l, char c) {
        _buffer.append( c );
    }

    /**
     * @see sexpression.lexer.ILexerState#readSpecial(sexpression.lexer.Lexer,
     *      sexpression.lexer.Token)
     */
    public void readSpecial(Lexer l, Token t) {
        l.add( new Word( _buffer.toString() ) );
        l.add( t );
        l.setState( WhitespaceState.SINGLETON );
    }

    /**
     * @see sexpression.lexer.ILexerState#readWhitespace(sexpression.lexer.Lexer)
     */
    public void readWhitespace(Lexer l) {
        l.add( new Word( _buffer.toString() ) );
        l.setState( WhitespaceState.SINGLETON );
    }

    /**
     * @see sexpression.lexer.ILexerState#readEOF(sexpression.lexer.Lexer)
     */
    public void readEOF(Lexer l) {
        l.add( new Word( _buffer.toString() ) );
        l.add( EOF.SINGLETON );
        l.setState( WhitespaceState.SINGLETON );
    }

    /**
     * @see sexpression.lexer.ILexerState#readComment(sexpression.lexer.Lexer)
     */
    public void readComment(Lexer l) {
        l.add( new Word( _buffer.toString() ) );
        l.setState( CommentState.SINGLETON );
    }

    /**
     * @see sexpression.lexer.ILexerState#readEOL(sexpression.lexer.Lexer)
     */
    public void readEOL(Lexer l) {
        l.add( new Word( _buffer.toString() ) );
        l.setState( WhitespaceState.SINGLETON );
    }
}
