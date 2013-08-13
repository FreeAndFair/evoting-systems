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

package sexpression.parser;

import sexpression.lexer.*;

/**
 * This visitor defines default behavior -- throw an exception in every case.
 * Selectively override these methods to denote acceptable cases in your
 * visitors.
 * 
 * @author kyle
 * 
 * @param <E>
 *            Set the return type of the visitor here.
 */
public class ATokenVisitor<E> implements ITokenVisitor<E> {

    /**
     * @see sexpression.lexer.ITokenVisitor#forClose(sexpression.lexer.Close)
     */
    public E forClose(Close c) {
        throw new UnexpectedTokenException( c.toString() );
    }

    /**
     * @see sexpression.lexer.ITokenVisitor#forColon(sexpression.lexer.Colon)
     */
    public E forColon(Colon c) {
        throw new UnexpectedTokenException( c.toString() );
    }

    /**
     * @see sexpression.lexer.ITokenVisitor#forOpen(sexpression.lexer.Open)
     */
    public E forOpen(Open o) {
        throw new UnexpectedTokenException( o.toString() );
    }

    /**
     * @see sexpression.lexer.ITokenVisitor#forWord(sexpression.lexer.Word)
     */
    public E forWord(Word w) {
        throw new UnexpectedTokenException( w.toString() );
    }

    /**
     * @see sexpression.lexer.ITokenVisitor#forEOF(sexpression.lexer.EOF)
     */
    public E forEOF(EOF e) {
        throw new UnexpectedTokenException( e.toString() );
    }

    /**
     * @see sexpression.lexer.ITokenVisitor#forHash(sexpression.lexer.Hash)
     */
    public E forHash(Hash hash) {
        throw new UnexpectedTokenException( hash.toString() );
    }

    /**
     * @see sexpression.lexer.ITokenVisitor#forMod(sexpression.lexer.Mod)
     */
    public E forMod(Mod mod) {
        throw new UnexpectedTokenException( mod.toString() );
    }

}
