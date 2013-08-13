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
 * <b>Visitor Design Pattern</b><br>
 * <br>
 * Instances of this interface can visit a Token. Implementers must define a
 * case for every concrete instance of Token.
 * 
 * @see sexpression.lexer.Token
 * @author kyle
 * 
 * @param <E>
 *            Specify the return type of the visitor execution here.
 */
public interface ITokenVisitor<E> {

    /**
     * Define the close case.
     * 
     * @see sexpression.lexer.Close
     */
    E forClose(Close c);

    /**
     * Define the open case.
     * 
     * @see sexpression.lexer.Open
     */
    E forOpen(Open o);

    /**
     * Define the colon case.
     * 
     * @see sexpression.lexer.Colon
     */
    E forColon(Colon c);

    /**
     * Define the word case.
     * 
     * @see sexpression.lexer.Word
     */
    E forWord(Word w);

    /**
     * Define the EOF case
     * 
     * @see sexpression.lexer.EOF
     */
    E forEOF(EOF e);

    /**
     * Define the Hash case
     * 
     * @see sexpression.lexer.Hash
     */
    E forHash(Hash hash);

    /**
     * Define the mod case
     * 
     * @see sexpression.lexer.Mod
     */
    E forMod(Mod mod);
}
