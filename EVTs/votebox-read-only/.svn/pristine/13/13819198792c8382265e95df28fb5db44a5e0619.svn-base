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
 * Each state instance must define the following, state-dependent behavior.
 * 
 * @author kyle
 * 
 */
public interface ILexerState {

    /**
     * Notify that a character has been read from the stream.
     * 
     * @param l
     *            This is the delegating instance.
     * @param b
     *            This is the character that was read.
     */
    public void readCharacter(Lexer l, char b);

    /**
     * Notify that whitespace has been read from the stream.
     * 
     * @param l
     *            This is the delegating instance.
     */
    public void readWhitespace(Lexer l);

    /**
     * Notify that an end-of-line has been read from the strem.
     * 
     * @param l
     *            This is the delegating instance.
     */
    public void readEOL(Lexer l);

    /**
     * Notify that a start-comment character has been read from the stream.
     * 
     * @param l
     *            This is the delegating instance.
     */
    public void readComment(Lexer l);

    /**
     * Notify that a special character (one that has a special token
     * correlation) has been read from the stream.
     * 
     * @param l
     *            This is the delegating instance.
     * @param t
     *            This is the token that represents the character that was read.
     */
    public void readSpecial(Lexer l, Token t);

    /**
     * Notify that the end of the stream has been reached.
     * 
     * @param l
     *            This is the delegating instance.
     */
    public void readEOF(Lexer l);
}
