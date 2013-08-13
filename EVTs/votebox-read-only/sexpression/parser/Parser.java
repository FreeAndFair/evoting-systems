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

import java.util.ArrayList;

import sexpression.lexer.*;
import sexpression.*;

/**
 * This is a concrete parser implementation. It recognizes the strings &#35;any,
 * &#35;string, &#35;list as being special, wildcard strings. &#35;list must be followed by
 * a colon and then an sexp which defines the body of the list wildcard.
 * 
 * @author kyle
 * 
 */
public class Parser implements IParser {

    public static final String ANY = "any";
    public static final String STRING = "string";
    public static final String LIST = "list";
    public static final String WILDCARD = "wildcard";
    public static final String NOMATCH = "nomatch";
    public static final String NOTHING = "nothing";

    private final ILexer _lexer;

    /**
     * Construct a parser which gets its token stream from the given lexer.
     * 
     * @param lex
     *            Get the tokens from here.
     */
    public Parser(ILexer lex) {
        _lexer = lex;
    }

    /**
     * @see sexpression.parser.IParser#read()
     */
    public ASExpression read() {
        return (ASExpression) _lexer.peek().execute(
            new ATokenVisitor<ASExpression>() {

                @Override
                public ASExpression forOpen(Open o) {
                    return parseList();
                }

                @Override
                public ASExpression forWord(Word w) {
                    return parseWord();
                }

                @Override
                public ASExpression forMod(Mod m) {
                    return parseName();
                }

                @Override
                public ASExpression forHash(Hash h) {
                    return parseWildcard();
                }
            } );
    }

    private ASExpression parseList() {
        ArrayList<ASExpression> list = new ArrayList<ASExpression>();

        _lexer.read();
        while (!(_lexer.peek() == Close.SINGLETON))
            list.add( read() );
        _lexer.read();

        return new ListExpression( list );
    }

    private ASExpression parseWord() {
        return StringExpression.makeString( ((Word) _lexer.read()).getWord() );
    }

    private ASExpression parseName() {
        _lexer.read();
        final Token name = _lexer.read();
        final Token colon = _lexer.read();

        return (ASExpression) name.execute( new ATokenVisitor<ASExpression>() {

            @Override
            public ASExpression forWord(final Word w) {
                return (ASExpression) colon
                        .execute( new ATokenVisitor<ASExpression>() {

                            @Override
                            public ASExpression forColon(Colon c) {
                                return new NamedPattern( w.getWord(), read() );
                            }

                        } );
            }

        } );
    }

    private ASExpression parseWildcard() {
        _lexer.read();
        final Token type = _lexer.read();

        return (ASExpression) type.execute( new ATokenVisitor<ASExpression>() {

            @Override
            public ASExpression forWord(final Word w) {
                String s = w.getWord();

                if (s.equals( ANY ))
                    return Wildcard.SINGLETON;
                if (s.equals( STRING ))
                    return StringWildcard.SINGLETON;
                if (s.equals( WILDCARD ))
                    return WildcardWildcard.SINGLETON;
                if (s.equals( NOTHING ))
                    return Nothing.SINGLETON;
                if (s.equals( NOMATCH ))
                    return NoMatch.SINGLETON;
                if (s.equals( LIST )) {
                    final Token colon = _lexer.read();
                    return (ASExpression) colon
                            .execute( new ATokenVisitor<ASExpression>() {

                                @Override
                                public ASExpression forColon(Colon c) {
                                    return new ListWildcard( read() );
                                }
                            } );
                }

                throw new UnexpectedTokenException( "#" + s.toString() );
            }

        } );
    }
}
